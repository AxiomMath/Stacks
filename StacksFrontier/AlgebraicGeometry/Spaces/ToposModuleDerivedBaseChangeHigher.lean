module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeDegreewise
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The base change map of Stacks 0736 as a map of higher direct images

Let

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

be a commutative square of algebraic spaces over a scheme `S` with `g^*` and `(g')^*` exact.
**Stacks 073K**, part (1) speaks about one morphism of `𝒪_{Y'}`-modules for each `i ≥ 0`,

`g^*R^if_*𝓕 ⟶ R^if'_*𝓕'`,  `𝓕' = (g')^*𝓕`,

with `R^if_*` the higher direct image this development writes as
`(AlgebraicGeometry.Space.modulePushforward B S hS f).rightDerived i`.  This file constructs that
morphism from the base change map of the bounded below derived category,
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap`, and proves that invertibility of the
two is the same thing in each degree.

With this, the only thing between the reduction of part (1) and the tag's own statement is the
invertibility, which is asserted nowhere; the map part (1) is about is here, in the source's
vocabulary.

## Main definitions

* `AlgebraicGeometry.Space.toposModulePushforwardIsoModulePushforward`: the ringed-topoi direct
  image *is* the modules development's direct image, up to the named isomorphism
  `AlgebraicGeometry.Space.modulePushforwardIso` of **Stacks 03D6**, part (1).
* `AlgebraicGeometry.Space.higherDirectImageBaseChangeSourceIso` and
  `…TargetIso`: the identifications of `g^*R^if_*` and of `R^if'_*(g')^*` with degree-`i`
  cohomology of the bounded below derived composites.
* `AlgebraicGeometry.Space.higherDirectImageBaseChangeMap`: **the base change map of
  Stacks 0736 as a morphism `g^*R^if_* ⟶ R^if'_*(g')^*` of higher direct images.**

## Main results

* `AlgebraicGeometry.Space.higherDirectImageBaseChangeMap_app`: it is the degree-`i` cohomology of
  the base change map at `𝓕` in degree zero, read through the two identifications.
* `AlgebraicGeometry.Space.isIso_higherDirectImageBaseChangeMap_app_iff`: **invertibility of it is
  invertibility of that cohomology map** — the two identifications are isomorphisms, so the
  assertion of part (1) is not invertibility of something invertible by construction.
* `AlgebraicGeometry.Space.isIso_higherDirectImageBaseChangeMap_app`: the direction part (1)
  consumes — invertibility in `D⁺` gives invertibility in each degree `i ≥ 0`.
* `AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_single_iff`: **part (1) in
  `D⁺` and part (1) in every degree `i ≥ 0` are the same statement**, for a coefficient placed in
  degree zero.  This is the join between the locality reduction, which concludes invertibility in
  `D⁺`, and the affine case, which is degreewise.

## Implementation notes

*The three crossings, and that they are now all performed.*  Three conventions had to be
reconciled, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleDerivedBaseChangeDegreewise.lean` named the first
two as owed.

* `R^if_*` of this development is `CategoryTheory.Functor.rightDerived`, the
  injective-resolution convention, whereas the base change map lives on the bounded below derived
  category.  `Stacks.DerivedIndexing.rightDerivedIso` crosses the two:
  `F.rightDerived i ≅ F.rightDerivedPlus (i : ℤ)`, the latter being by definition
  `singleFunctor 0 ⋙ F.rightDerivedFunctorPlus ⋙ homologyFunctor i`.
* `𝓕' = (g')^*𝓕` is the module inverse image, whereas the base change map is applied to the
  *derived* inverse image of `𝓕` placed in degree zero.  For an exact `(g')^*` the two agree, and
  `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` is the identification.
* The direct image is written two ways in this development.  `R^if_*` is
  `AlgebraicGeometry.Space.modulePushforward`, while the base change map and the pasting law of
  **Stacks 0E47** are seated at `AlgebraicGeometry.Space.toposModulePushforward`, whose declared
  type is already at `AlgebraicGeometry.Space.Modules` — that seating is what makes the pasting
  law elaborable at all, as the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleDerivedBaseChangeHorizontal.lean` record.  The
  two differ by `AlgebraicGeometry.Space.modulePushforwardIso`, and
  `toposModulePushforwardIsoModulePushforward` below is that isomorphism with its source read at
  `toposModulePushforward`, which it is by definition:  `toposModulePushforward f` is
  `Stacks.Sheaves.RingedToposModules.pushforwardModules` of
  `AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom` on the nose.
  `CategoryTheory.Functor.rightDerivedIsoOfNatIso` carries it to the higher direct images.

*Why the degrees are `ℕ`, and why that loses nothing.*
`CategoryTheory.Functor.rightDerived` is indexed by `ℕ`, and part (1) asserts its clause for
`i ≥ 0`, so the two agree.  `CategoryTheory.DerivedCategory.Plus.isIso_iff` however quantifies over
all of `ℤ`, so passing from the `ℕ`-indexed family back to `D⁺` looks as though it needed the
negative degrees — and it does, but they are free:  a module placed in degree zero is `IsGE 0`, and
`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj` says the bounded below right derived
functor of an additive functor preserves a lower bound, so both sides of the base change map at
such a coefficient are `IsGE 0` and their cohomology below degree zero is zero.  A morphism between
zero objects is invertible, so the negative degrees impose nothing and
`isIso_toposModuleDerivedBaseChangeMap_app_single_iff` is a genuine equivalence.  That is the join
between the two halves of a proof of part (1):  the locality reduction of
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleDerivedBaseChangeChartwise.lean` concludes
invertibility in `D⁺`, and the affine case the source reduces part (1) to is a statement about one
degree at a time.  The `ℤ`-indexed equivalence at the bounded below convention, for an arbitrary
coefficient of `D⁺`, is `AlgebraicGeometry.Space.isIso_toposModuleHomologyBaseChangeMap_iff`.

*This is not Stacks 073K, part (1).*  Nothing below asserts that any map is invertible.  Part (1)
asserts invertibility, for a cartesian square with `g` flat and `f` quasi-compact and
quasi-separated; the main results here are an equivalence between two invertibility statements and
an implication between two others.  No `@[stacks 073K]` attribute is carried, and the part-(2)
carrier `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase` is
untouched.  The same construction for a cartesian square of *schemes*, for the comparison map of
**Stacks 0GN5**, is
`StacksFrontier/AlgebraicGeometry/FlatModuleCohomologyBaseChange/DegreewiseComparison.lean`, and this
file is that one transported to the seating of algebraic spaces.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] enoughInjectives_modules

-- The standard derived category of the `𝒪`-modules of an algebraic space, pinned so that it is
-- the witness instance search produces; `HasDerivedCategory` is data, so the statements composed
-- here are only composable against the witness they were elaborated with.  The pin itself is the
-- one declared in `ToposModuleDerivedBaseChangeDegreewise.lean`, reused rather than restated.
attribute [local instance] degreewiseBaseChangeHasDerivedCategory

/-- Injective resolutions of the `𝒪`-modules of an algebraic space, which is what
`CategoryTheory.Functor.rightDerived` asks for.  This is
`AlgebraicGeometry.Space.hasInjectiveResolutions_modules`, restated so that instance search finds
it with the universes fixed. -/
local instance higherBaseChangeHasInjectiveResolutions (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasInjectiveResolutions (Modules.{u, u} B S hS F hF) :=
  hasInjectiveResolutions_modules B S hS F hF

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y Y' : AlgebraicSpaces B S hS}

/-! ### The direct image at the two seatings -/

/-- **The ringed-topoi direct image is the modules development's direct image.**  This is the
isomorphism `AlgebraicGeometry.Space.modulePushforwardIso` of **Stacks 03D6**, part (1), with its
source read at `AlgebraicGeometry.Space.toposModulePushforward`, which it is by definition. -/
def toposModulePushforwardIsoModulePushforward (f : X ⟶ Y) :
    toposModulePushforward f ≅ modulePushforward B S hS f :=
  modulePushforwardIso B S hS f

/-- The higher direct images at the two seatings agree:
`CategoryTheory.Functor.rightDerivedIsoOfNatIso` applied to
`toposModulePushforwardIsoModulePushforward`. -/
def higherDirectImageIso (f : X ⟶ Y) (i : ℕ) :
    (toposModulePushforward f).rightDerived i ≅ (modulePushforward B S hS f).rightDerived i :=
  Functor.rightDerivedIsoOfNatIso (toposModulePushforwardIsoModulePushforward f) i

/-! ### The two identifications of the degreewise sides -/

section Square

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)]
    [PreservesFiniteLimits (modulePullback B S hS g')]
    [PreservesFiniteColimits (modulePullback B S hS g')]

/-- The identification of `g^*R^if_*` with the degree-`i` cohomology of the bounded below derived
source `(g^*)^+ ∘ Rf_*`:  the two seatings of the direct image, the crossing of the
injective-resolution and bounded below conventions, and the comparison of the exact `g^*` with
cohomology. -/
def higherDirectImageBaseChangeSourceIso (i : ℕ) :
    (modulePushforward B S hS f).rightDerived i ⋙ modulePullback B S hS g ≅
      DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0 ⋙
        (toposModulePushforward f).rightDerivedFunctorPlus ⋙
        (modulePullback B S hS g).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) (i : ℤ) :=
  Functor.isoWhiskerRight (higherDirectImageIso f i).symm (modulePullback B S hS g) ≪≫
    Functor.isoWhiskerRight
        (Stacks.DerivedIndexing.rightDerivedIso (toposModulePushforward f) i)
        (modulePullback B S hS g) ≪≫
      Functor.isoWhiskerLeft
        (DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0 ⋙
          (toposModulePushforward f).rightDerivedFunctorPlus)
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
          (modulePullback B S hS g) (i : ℤ)).symm

/-- The identification of `R^if'_*(g')^*` with the degree-`i` cohomology of the bounded below
derived target `Rf'_* ∘ ((g')^*)^+`:  the two seatings of the direct image, the crossing of the
injective-resolution and bounded below conventions, and the comparison of the exact `(g')^*` with
the degree-zero embedding — which is what identifies the derived inverse image of `𝓕[0]` with
`𝓕' = (g')^*𝓕` in degree zero. -/
def higherDirectImageBaseChangeTargetIso (i : ℕ) :
    modulePullback B S hS g' ⋙ (modulePushforward B S hS f').rightDerived i ≅
      DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0 ⋙
        (modulePullback B S hS g').rightDerivedFunctorPlus ⋙
        (toposModulePushforward f').rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) (i : ℤ) :=
  Functor.isoWhiskerLeft (modulePullback B S hS g') (higherDirectImageIso f' i).symm ≪≫
    Functor.isoWhiskerLeft (modulePullback B S hS g')
        (Stacks.DerivedIndexing.rightDerivedIso (toposModulePushforward f') i) ≪≫
      Functor.isoWhiskerRight
        (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (modulePullback B S hS g') 0)
        ((toposModulePushforward f').rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) (i : ℤ))

/-! ### The base change map of higher direct images -/

/-- **The base change map of Stacks 0736 as a morphism of higher direct images**,

`g^*R^if_*𝓕 ⟶ R^if'_*((g')^*𝓕)`.

It is the degree-`i` cohomology of `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap` at
`𝓕` placed in degree zero, transported along the two identifications
`higherDirectImageBaseChangeSourceIso` and `higherDirectImageBaseChangeTargetIso`.  This is the
morphism **Stacks 073K**, part (1) asserts to be an isomorphism;  nothing here asserts that. -/
def higherDirectImageBaseChangeMap (comm : g' ≫ f = f' ≫ g) (i : ℕ) :
    (modulePushforward B S hS f).rightDerived i ⋙ modulePullback B S hS g ⟶
      modulePullback B S hS g' ⋙ (modulePushforward B S hS f').rightDerived i :=
  (higherDirectImageBaseChangeSourceIso f g i).hom ≫
    Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0)
      (Functor.whiskerRight (toposModuleDerivedBaseChangeMap f g f' g' comm)
        (DerivedCategory.Plus.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) (i : ℤ))) ≫
    (higherDirectImageBaseChangeTargetIso f' g' i).inv

/-- The component of the base change map of higher direct images at a module `𝓕`, written as the
composite of the two identifications with the degree-`i` cohomology of the base change map of
`D⁺`. -/
theorem higherDirectImageBaseChangeMap_app (comm : g' ≫ f = f' ≫ g) (i : ℕ)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) :
    (higherDirectImageBaseChangeMap f g f' g' comm i).app 𝓕 =
      (higherDirectImageBaseChangeSourceIso f g i).hom.app 𝓕 ≫
        (DerivedCategory.Plus.homologyFunctor
            (Modules.{u, u} B S hS Y'.1 Y'.2) (i : ℤ)).map
          ((toposModuleDerivedBaseChangeMap f g f' g' comm).app
            ((DerivedCategory.Plus.singleFunctor
              (Modules.{u, u} B S hS X.1 X.2) 0).obj 𝓕)) ≫
        (higherDirectImageBaseChangeTargetIso f' g' i).inv.app 𝓕 := by
  simp only [higherDirectImageBaseChangeMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]

/-- **The base change map of higher direct images is invertible exactly when the degree-`i`
cohomology of the base change map of `D⁺` is.**  The two identifications it is defined through are
isomorphisms, so part (1)'s assertion in degree `i` and that cohomology map stand or fall
together; in particular part (1) is not invertibility of something invertible by construction. -/
theorem isIso_higherDirectImageBaseChangeMap_app_iff (comm : g' ≫ f = f' ≫ g) (i : ℕ)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((higherDirectImageBaseChangeMap f g f' g' comm i).app 𝓕) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor
          (Modules.{u, u} B S hS Y'.1 Y'.2) (i : ℤ)).map
        ((toposModuleDerivedBaseChangeMap f g f' g' comm).app
          ((DerivedCategory.Plus.singleFunctor
            (Modules.{u, u} B S hS X.1 X.2) 0).obj 𝓕))) := by
  rw [higherDirectImageBaseChangeMap_app, isIso_comp_left_iff, isIso_comp_right_iff]

/-- **Stacks 073K, part (1) in each degree follows from part (1) in `D⁺`.**  If the base change map
of **Stacks 0736** is invertible as a morphism of `D⁺(𝒪_{Y'})` at `𝓕` placed in degree zero, then
the base change map of higher direct images `g^*R^if_*𝓕 ⟶ R^if'_*((g')^*𝓕)` is invertible for
every `i ≥ 0`.

This is the direction a proof of part (1) runs in; it asserts nothing about invertibility
itself. -/
theorem isIso_higherDirectImageBaseChangeMap_app (comm : g' ≫ f = f' ≫ g)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2)
    (h𝓕 : IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app
      ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj 𝓕)))
    (i : ℕ) :
    IsIso ((higherDirectImageBaseChangeMap f g f' g' comm i).app 𝓕) := by
  rw [isIso_higherDirectImageBaseChangeMap_app_iff]
  exact Functor.map_isIso _ _

/-- **Part (1) in `D⁺` and part (1) in every degree `i ≥ 0` are the same statement**, for a
coefficient placed in degree zero.

This is the join between the two halves of a proof of **Stacks 073K**, part (1):  the locality
reduction `AlgebraicGeometry.Space.isIso_toposModuleDerivedBaseChangeMap_app_of_forall_chart`
concludes invertibility in `D⁺`, while the affine case the source reduces to is a statement about
one degree at a time, and `ℕ` does not reach the negative degrees that
`CategoryTheory.DerivedCategory.Plus.isIso_iff` quantifies over.  It does not have to:  a module
placed in degree zero is `IsGE 0`, the bounded below right derived functor of an additive functor
preserves a lower bound
(`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`), so both sides of the base change map
are `IsGE 0` and their negative cohomology vanishes — a morphism between zero objects is
invertible with nothing assumed. -/
theorem isIso_toposModuleDerivedBaseChangeMap_app_single_iff (comm : g' ≫ f = f' ≫ g)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app
        ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj 𝓕)) ↔
      ∀ i : ℕ, IsIso ((higherDirectImageBaseChangeMap f g f' g' comm i).app 𝓕) := by
  refine ⟨isIso_higherDirectImageBaseChangeMap_app f g f' g' comm 𝓕, fun h => ?_⟩
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  rcases lt_or_ge n 0 with hn | hn
  · -- the coefficient sits in degree zero, so both sides are bounded below by `0`
    have := Functor.isGE_rightDerivedFunctorPlus_obj (toposModulePushforward f)
      ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj 𝓕) 0
    have := Functor.isGE_rightDerivedFunctorPlus_obj (modulePullback B S hS g')
      ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj 𝓕) 0
    have := Functor.isGE_rightDerivedFunctorPlus_obj (modulePullback B S hS g)
      ((toposModulePushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj 𝓕)) 0
    have := Functor.isGE_rightDerivedFunctorPlus_obj (toposModulePushforward f')
      ((modulePullback B S hS g').rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj 𝓕)) 0
    dsimp only [Functor.comp_obj]
    exact IsZero.isIso (DerivedCategory.Plus.isZero_homology_of_isGE' _ 0 n hn)
      (DerivedCategory.Plus.isZero_homology_of_isGE' _ 0 n hn) _
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact (isIso_higherDirectImageBaseChangeMap_app_iff f g f' g' comm i 𝓕).1 (h i)

end Square

end AlgebraicGeometry.Space

end
