module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom

/-!
# The derived adjunction, composition and base change for algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and `φ_f` the morphism of small étale ringed topoi of Stacks 03G8.  The derived direct
image is `Rf_* = Stacks.Cohomology.DerivedPushforward.derivedPushforward φ_f` and the derived
pullback is `Lf^* = AlgebraicGeometry.Space.smallEtaleDerivedModulePullback f`.  This file
assembles, for morphisms of algebraic spaces and with no hypothesis, the adjunction
`Lf^* ⊣ Rf_*` (Stacks 07A6), the composition law `Lf^* ∘ Lg^* ≅ L(g ∘ f)^*` (Stacks 0D6D), and
the base change map `Lg^* Rf_* ⟶ Rf'_* L(g')^*` of a commutative square (Stacks 07A7).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModuleAdjunction`: `Lf^* ⊣ Rf_*`.
* `AlgebraicGeometry.Space.pullbackModulesIsoModulePullback`: the pullback of modules of `φ_f`
  is `AlgebraicGeometry.Space.modulePullback`, the left-adjoint form of
  `AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`: `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`.
* `AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap`: the base change map
  `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` of a commutative square of algebraic spaces.

## Implementation notes

The morphism of ringed topoi of a composite `f ≫ g` is not the composite `φ_g ∘ φ_f` but only
2-isomorphic to it, the comparison being `AlgebraicGeometry.Space.pushforwardModulesCompTransport`
on direct images.  The composition law is therefore the ringed-topos Stacks 0D6D,
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackCompIso`, followed by the
action of that 2-isomorphism on derived pullbacks,
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackIsoOfPullbackModulesIso`.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy)

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The modules on the small étale ringed topos of an algebraic space form a Grothendieck
abelian category, in the spelling over which the derived direct image of a morphism of ringed
topoi is formed. -/
instance isGrothendieckAbelian_ringedToposStructureRingSheaf (X : AlgebraicSpaces B S hS) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  isGrothendieckAbelian_modules B S hS X.1 X.2

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The direct image of modules along the morphism of small étale ringed topoi of a morphism of
algebraic spaces is additive. -/
instance additive_smallEtaleRingedToposHom_pushforwardModules (f : X ⟶ Y) :
    (RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).Additive :=
  RingedToposHom.pushforwardModules_additive (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- The composite `φ_g ∘ φ_f` of the morphisms of small étale ringed topoi of `f` and `g`. -/
abbrev smallEtaleRingedToposHomComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Z) :=
  RingedToposHom.comp (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (Z := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS g)
    (smallEtaleRingedToposHom B S hS f)

/-- The derived pullback along the composite `φ_g ∘ φ_f` exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_smallEtaleRingedToposHomComp
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackOnHomotopy (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
      (smallEtaleRingedToposHomComp B S hS f g)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := smallEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHomComp B S hS f g)

/-! ### The adjunction `Lf^* ⊣ Rf_*` -/

/-- **The derived adjunction for a morphism of algebraic spaces**, `Lf^* ⊣ Rf_*` on the
unbounded derived categories of modules on the small étale sites: Stacks 07A6 for the morphism of
small étale ringed topoi of Stacks 03G8. -/
def smallEtaleDerivedModuleAdjunction (f : X ⟶ Y) :
    smallEtaleDerivedModulePullback B S hS f ⊣
      derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f) :=
  derivedAdjunction (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)

/-- The derived adjunction `Lf^* ⊣ Rf_*` of a morphism of algebraic spaces is compatible with the
shifts of the two derived categories. -/
instance smallEtaleDerivedModuleAdjunction_commShift (f : X ⟶ Y) :
    (smallEtaleDerivedModuleAdjunction B S hS f).CommShift ℤ :=
  derivedAdjunction_commShift (X := smallEtaleRingedTopos B S hS _)
    (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)

/-- The pullback of modules of the morphism of small étale ringed topoi is
`AlgebraicGeometry.Space.modulePullback`: both are left adjoint to the direct image, the two
spellings of which agree by `pushforwardModulesIsoModulePushforward`. -/
def pullbackModulesIsoModulePullback (f : X ⟶ Y) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f).toModulesHom ≅
      modulePullback B S hS f :=
  (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).leftAdjointUniq
    ((modulePullbackAdjunction B S hS f).ofNatIsoRight
      (pushforwardModulesIsoModulePushforward B S hS f).symm)

/-! ### Composition, Stacks 0D6D -/

/-- The pullback of modules along the composite of the morphisms of small étale ringed topoi of
`f` and `g` is the pullback along the morphism of ringed topoi of `f ≫ g`: both are left
adjoint to the direct image of the composite, compared by
`AlgebraicGeometry.Space.pushforwardModulesCompTransport`. -/
def pullbackModulesCompTransport (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHomComp B S hS f g).toModulesHom ≅
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS (f ≫ g)).toModulesHom :=
  (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Z)
      (smallEtaleRingedToposHomComp B S hS f g)).leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS (f ≫ g))).ofNatIsoRight
        (pushforwardModulesCompTransport B S hS f g).symm)

/-- **Stacks 0D6D for algebraic spaces.**  For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of
algebraic spaces, `Lf^* ∘ Lg^* ≅ L(g ∘ f)^*` as functors `D(𝒪_Z) ⥤ D(𝒪_X)`. -/
def smallEtaleDerivedModulePullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleDerivedModulePullback B S hS g ⋙ smallEtaleDerivedModulePullback B S hS f ≅
      smallEtaleDerivedModulePullback B S hS (f ≫ g) :=
  derivedPullbackCompIso (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (Z := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g) ≪≫
    derivedPullbackIsoOfPullbackModulesIso (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Z) (φ := smallEtaleRingedToposHomComp B S hS f g)
      (ψ := smallEtaleRingedToposHom B S hS (f ≫ g)) (pullbackModulesCompTransport B S hS f g)

/-- Equal morphisms of algebraic spaces have isomorphic derived pullbacks. -/
def smallEtaleDerivedModulePullbackCongr {f f' : X ⟶ Y} (h : f = f') :
    smallEtaleDerivedModulePullback B S hS f ≅ smallEtaleDerivedModulePullback B S hS f' :=
  eqToIso (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) h)

/-! ### The base change map, Stacks 07A7 -/

section BaseChange

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- The iterated derived pullback `Lf^* ⋙ L(g')^*` around the top and right of a commutative
square, identified with the derived pullback along the common composite `f' ≫ g`. -/
def smallEtaleDerivedModulePullbackSquareIso :
    smallEtaleDerivedModulePullback B S hS f ⋙ smallEtaleDerivedModulePullback B S hS g' ≅
      smallEtaleDerivedModulePullback B S hS (f' ≫ g) :=
  smallEtaleDerivedModulePullbackCompIso B S hS g' f ≪≫
    smallEtaleDerivedModulePullbackCongr B S hS w

/-- **The derived base change morphism of functors** `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` of a
commutative square of algebraic spaces: the mate, under the derived adjunctions, of the
comparison of the two iterated derived pullbacks around the square. -/
def smallEtaleDerivedBaseChangeSquare :
    TwoSquare (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f))
      (smallEtaleDerivedModulePullback B S hS g') (smallEtaleDerivedModulePullback B S hS g)
      (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')) :=
  Stacks.CategoryTheory.BaseChange.twoSquare (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w)

/-- **The base change map for algebraic spaces**, Stacks 07A7 for a commutative square
`g' ≫ f = f' ≫ g` of algebraic spaces: the canonical map `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` in
`D(𝒪_{Y'})`, adjoint to `L(g')^*` of the counit `Lf^* Rf_* K ⟶ K` after identifying
`L(f')^* Lg^*` with `L(g')^* Lf^*`. -/
def smallEtaleDerivedModuleBaseChangeMap
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedModulePullback B S hS g).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K) ⟶
      (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).obj
        ((smallEtaleDerivedModulePullback B S hS g').obj K) :=
  Stacks.CategoryTheory.BaseChange.map (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w) K

/-- **The base change map is the transpose of `L(g')^*` of the counit.**  Under
`L(f')^* ⊣ Rf'_*` the base change map is the comparison of the two iterated derived pullbacks
followed by `L(g')^*` of the counit of `Lf^* ⊣ Rf_*`; this determines it. -/
theorem smallEtaleDerivedModuleBaseChangeMap_adjoint
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedModuleAdjunction B S hS f').homEquiv _ _).symm
        (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K) =
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g).hom.app _ ≫
        (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w).inv.app _ ≫
        (smallEtaleDerivedModulePullback B S hS g').map
          ((smallEtaleDerivedModuleAdjunction B S hS f).counit.app K) :=
  Stacks.CategoryTheory.BaseChange.homEquiv_symm_map (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w) K

/-- The base change map is natural in `K`. -/
theorem smallEtaleDerivedModuleBaseChangeMap_naturality
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (e : K ⟶ L) :
    (smallEtaleDerivedModulePullback B S hS g).map
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).map e) ≫
        smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w L =
      smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K ≫
        (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).map
          ((smallEtaleDerivedModulePullback B S hS g').map e) :=
  Stacks.CategoryTheory.BaseChange.map_naturality (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w) e

end BaseChange

end AlgebraicGeometry.Space

end
