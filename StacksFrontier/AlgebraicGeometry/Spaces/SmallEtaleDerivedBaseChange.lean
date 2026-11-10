module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExists
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison

/-!
# The derived base change map for a commutative square of algebraic spaces

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a commutative square of algebraic spaces over a scheme `S`. This file constructs the derived
direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` together with its adjunction `Lf^* ⊣ Rf_*`
(Stacks 07A6), the composition isomorphism `Lf^* ∘ Lg^* ≅ L(g ∘ f)^*` of derived pullbacks
along morphisms of algebraic spaces (Stacks 0D6D), and the canonical base change map

`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`,

the mate under the two derived adjunctions of the comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ L(g')^*`
of the two iterated derived pullbacks around the square. This is the base change map that
Stacks 0DKH and 08JQ assert to be an isomorphism under their hypotheses.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePushforward`: `Rf_*`.
* `AlgebraicGeometry.Space.smallEtaleDerivedAdjunction`: `Lf^* ⊣ Rf_*`.
* `AlgebraicGeometry.Space.smallEtaleModulePullbackToposCompIso`: the degreewise pullback along
  the composite of the morphisms of ringed topoi is the pullback along the morphism of ringed
  topoi of the composite.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackCompIso`: `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackSquareIso`: the comparison of the two
  iterated derived pullbacks around a commutative square.
* `AlgebraicGeometry.Space.smallEtaleDerivedBaseChange`: the base change transformation
  `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*`, and `smallEtaleDerivedBaseChangeMap` its component.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeMap_adjoint`: under `Lf'^* ⊣ Rf'_*` the
  base change map is the derived pullback along `g'` of the counit of `Lf^* ⊣ Rf_*`, read
  through the comparison of the iterated pullbacks.
* `AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeMap_naturality`: naturality.

## Implementation notes

The morphism of small étale ringed topoi attached to a composite of morphisms of algebraic
spaces is not the composite of the two morphisms of ringed topoi; their pullbacks of modules are
canonically isomorphic (Stacks 03LU, `AlgebraicGeometry.Space.modulePullbackCompIso`), and the
derived pullbacks are compared through
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackIsoOfIso`.

`Rf_*` is the derived direct image of the morphism of small étale ringed topoi of `f`, the
right adjoint of `Lf^*` of Stacks 07A6 for a morphism of ringed topoi.

The base change map of Stacks 08HY is defined for ringed spaces; this is the same construction
for algebraic spaces.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0DKH](https://stacks.math.columbia.edu/tag/0DKH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace AlgebraicGeometry.Space

universe u

/-- A component of the mate of a two-square, transposed back across the second adjunction, is the
two-square followed by the image of the first counit.  This is `CategoryTheory.mateEquiv_counit`
read through `Adjunction.homEquiv`; it is stated for arbitrary adjunctions so that its
instantiations at derived functors do not ask the kernel to unfold them. -/
theorem homEquiv_symm_mateEquiv_app {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (d : D) :
    (adj₂.homEquiv _ _).symm ((mateEquiv adj₁ adj₂ α).app d) =
      α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d) := by
  rw [Adjunction.homEquiv_counit, mateEquiv_counit]

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheaves of modules on the small étale ringed topos of an algebraic space form a Grothendieck
abelian category at the universe of the structure rings, in the spelling the derived direct
image of a morphism of ringed topoi asks for. -/
instance isGrothendieckAbelian_smallEtaleRingedToposModules (X : AlgebraicSpaces B S hS) :
    IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS X).O)) :=
  isGrothendieckAbelian_modules B S hS X.1 X.2

variable {X Y Z X' Y' : AlgebraicSpaces B S hS}

/-- **The derived direct image `Rf_*`** along a morphism of algebraic spaces: the total right
derived functor of the degreewise direct image of the morphism of small étale ringed topoi. -/
abbrev smallEtaleDerivedModulePushforward (f : X ⟶ Y) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
  Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- **Stacks 07A6 for a morphism of algebraic spaces**: `Lf^* ⊣ Rf_*`. -/
def smallEtaleDerivedAdjunction (f : X ⟶ Y) :
    smallEtaleDerivedModulePullback B S hS f ⊣ smallEtaleDerivedModulePushforward B S hS f :=
  derivedAdjunction (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f)

/-- The degreewise pullback of modules along the composite of the morphisms of small étale ringed
topoi of `f` and `g` is the degreewise pullback along the morphism of ringed topoi of `f ≫ g`:
the strict compositor of Stacks 03D6 followed by the composition comparison of Stacks 03LU. -/
def smallEtaleModulePullbackToposCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((smallEtaleRingedToposHom B S hS g).comp
        (smallEtaleRingedToposHom B S hS f)).toModulesHom.pullbackModules ≅
      (smallEtaleRingedToposHom B S hS (f ≫ g)).toModulesHom.pullbackModules :=
  RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g) ≪≫
    Functor.isoWhiskerRight (eqToIso (congrArg (fun h => h.pullbackModules)
      (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
        (smallEtaleRingedToposHom B S hS g)))) _ ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (congrArg (fun h => h.pullbackModules)
      (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
        (smallEtaleRingedToposHom B S hS f)))) ≪≫
    modulePullbackCompIso B S hS f g ≪≫
    eqToIso (congrArg (fun h => h.pullbackModules)
      (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
        (smallEtaleRingedToposHom B S hS (f ≫ g)))).symm

/-- **Stacks 0D6D for morphisms of algebraic spaces.** `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`. -/
def smallEtaleDerivedPullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleDerivedModulePullback B S hS g ⋙ smallEtaleDerivedModulePullback B S hS f ≅
      smallEtaleDerivedModulePullback B S hS (f ≫ g) :=
  haveI : (pullbackOnHomotopy (RingedToposHom.comp (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
      (smallEtaleRingedToposHom B S hS g)
      (smallEtaleRingedToposHom B S hS f))).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := smallEtaleRingedTopos B S hS Z)) :=
    hasLeftDerivedFunctor_pullbackOnHomotopy (compRingedToposHom B S hS f g)
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackCompIso
      (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g) ≪≫
    derivedPullbackIsoOfIso _ _ (smallEtaleModulePullbackToposCompIso B S hS f g)

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- The comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ L(g')^*` of the two iterated derived pullbacks around a
commutative square of algebraic spaces: both are the derived pullback along the common composite
of the square. -/
def smallEtaleDerivedPullbackSquareIso :
    smallEtaleDerivedModulePullback B S hS g ⋙ smallEtaleDerivedModulePullback B S hS f' ≅
      smallEtaleDerivedModulePullback B S hS f ⋙ smallEtaleDerivedModulePullback B S hS g' :=
  smallEtaleDerivedPullbackCompIso B S hS f' g ≪≫
    eqToIso (congrArg (fun k : X' ⟶ Y => smallEtaleDerivedModulePullback B S hS k) w.symm) ≪≫
    (smallEtaleDerivedPullbackCompIso B S hS g' f).symm

/-- **The derived base change transformation** `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` of a commutative
square of algebraic spaces: the mate, under `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`, of the comparison
of the two iterated derived pullbacks. -/
def smallEtaleDerivedBaseChange :
    TwoSquare (smallEtaleDerivedModulePushforward B S hS f)
      (smallEtaleDerivedModulePullback B S hS g') (smallEtaleDerivedModulePullback B S hS g)
      (smallEtaleDerivedModulePushforward B S hS f') :=
  mateEquiv (smallEtaleDerivedAdjunction B S hS f) (smallEtaleDerivedAdjunction B S hS f')
    (TwoSquare.mk _ _ _ _ (smallEtaleDerivedPullbackSquareIso B S hS f g f' g' w).hom)

/-- **The derived base change map** `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`. -/
def smallEtaleDerivedBaseChangeMap
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedModulePullback B S hS g).obj
        ((smallEtaleDerivedModulePushforward B S hS f).obj K) ⟶
      (smallEtaleDerivedModulePushforward B S hS f').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj K) :=
  (smallEtaleDerivedBaseChange B S hS f g f' g' w).app K

/-- The derived base change transformation is the mate, under `Lf^* ⊣ Rf_*` and
`Lf'^* ⊣ Rf'_*`, of the comparison `smallEtaleDerivedPullbackSquareIso`. -/
theorem smallEtaleDerivedBaseChange_eq :
    smallEtaleDerivedBaseChange B S hS f g f' g' w =
      mateEquiv (smallEtaleDerivedAdjunction B S hS f) (smallEtaleDerivedAdjunction B S hS f')
        (TwoSquare.mk _ _ _ _ (smallEtaleDerivedPullbackSquareIso B S hS f g f' g' w).hom) := by
  unfold smallEtaleDerivedBaseChange
  rfl

/-- Under `Lf'^* ⊣ Rf'_*` the base change map is the derived pullback along `g'` of the counit
`Lf^* Rf_* K ⟶ K`, read through the comparison of the two iterated derived pullbacks. -/
theorem smallEtaleDerivedBaseChangeMap_adjoint
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedAdjunction B S hS f').homEquiv _ _).symm
        (smallEtaleDerivedBaseChangeMap B S hS f g f' g' w K) =
      (smallEtaleDerivedPullbackSquareIso B S hS f g f' g' w).hom.app
          ((smallEtaleDerivedModulePushforward B S hS f).obj K) ≫
        (smallEtaleDerivedModulePullback B S hS g').map
          ((smallEtaleDerivedAdjunction B S hS f).counit.app K) := by
  rw [smallEtaleDerivedBaseChangeMap, smallEtaleDerivedBaseChange_eq]
  exact homEquiv_symm_mateEquiv_app _ _ _ K

/-- The derived base change map is natural in the complex. -/
theorem smallEtaleDerivedBaseChangeMap_naturality
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (a : K ⟶ L) :
    (smallEtaleDerivedModulePullback B S hS g).map
          ((smallEtaleDerivedModulePushforward B S hS f).map a) ≫
        smallEtaleDerivedBaseChangeMap B S hS f g f' g' w L =
      smallEtaleDerivedBaseChangeMap B S hS f g f' g' w K ≫
        (smallEtaleDerivedModulePushforward B S hS f').map
          ((smallEtaleDerivedModulePullback B S hS g').map a) :=
  (smallEtaleDerivedBaseChange B S hS f g f' g' w).naturality a

end AlgebraicGeometry.Space

end
