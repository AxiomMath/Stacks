module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DerivedLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeMap

/-!
# The base change map of Stacks 0736 for algebraic spaces, read in each degree

Let

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

be a commutative square of algebraic spaces over a scheme `S` whose inverse image `g^*` of
`𝒪`-modules is exact.  The base change map of **Stacks 0736** at the seating of the modules
development, `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap`, is a morphism of the
bounded below derived category `D⁺(𝒪_{Y'})`, whereas **Stacks 073K**, part (1) speaks about one
morphism of `𝒪_{Y'}`-modules for each degree.  This file constructs the degreewise morphism and
proves that invertibility of the two is the same thing.

Since `g^*` is exact, its bounded below right derived functor commutes with cohomology —
`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso` — so `H^i` of the base change map at an
object `M` of `D⁺(𝒪_X)` may be read as a morphism

`g^*H^i(Rf_*M) ⟶ H^i(Rf'_*((g')^*M))`

out of the inverse image of the degree-`i` cohomology of the derived direct image.  That is the
degreewise base change map below.

## Main definitions

* `AlgebraicGeometry.Space.toposModuleHomologyBaseChangeMap`: **the base change map in degree
  `i`**, `g^*H^i(Rf_*M) ⟶ H^i(Rf'_*((g')^*M))`.

## Main results

* `AlgebraicGeometry.Space.isIso_toposModuleHomologyBaseChangeMap_iff`: **the degreewise maps are
  all invertible exactly when the map of `D⁺` is.**
* `AlgebraicGeometry.Space.isIso_toposModuleHomologyBaseChangeMap`: the direction part (1)
  consumes — invertibility in `D⁺` gives invertibility in each degree.

## Implementation notes

*What is and is not identified.*  The degreewise map below is the degree-`i` cohomology of the
base change map, with its source rewritten by the comparison of the derived inverse image with
cohomology.  Its target is the degree-`i` cohomology of `Rf'_*` applied to the *derived* inverse
image of `M`.  For `M` a single `𝒪_X`-module in degree zero and an exact `(g')^*` the derived
inverse image is the module inverse image in degree zero, so this is the `ℱ' = (g')^*ℱ` of the
source; that identification is
`Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` together with the crossing
`Stacks.DerivedIndexing.rightDerivedIso` between the injective-resolution convention of
`CategoryTheory.Functor.rightDerived`, which is what the development's `R^if_*` for algebraic
spaces is written with, and the bounded below convention used here.  Neither crossing is
performed below, so what is constructed is the degreewise base change map at the bounded below
convention and read at a derived coefficient, and not yet the morphism
`g^*R^if_*ℱ ⟶ R^if'_*ℱ'` written in the source's own vocabulary.  The scheme analogue of both
crossings is carried out in
`StacksFrontier/AlgebraicGeometry/FlatModuleCohomologyBaseChange/DegreewiseComparison.lean`, for the
comparison map of **Stacks 0GN5**.

*Why the equivalence is not vacuous.*  The source of the degreewise map is reached from `H^i` of
the derived source by an isomorphism, so invertibility of the degreewise map is invertibility of
`H^i` of the base change map and of nothing else; a morphism of `D⁺` is invertible exactly when
all of its cohomology maps are, which is
`CategoryTheory.DerivedCategory.Plus.isIso_iff`.  Both halves of the equivalence below are
therefore about the base change map itself and not about a comparison invertible by
construction.

*This is not Stacks 073K, part (1).*  Part (1) asserts that the map *is* invertible, for a
cartesian square with `g` flat and `f` quasi-compact and quasi-separated.  Nothing below asserts
invertibility of anything: the main result is an equivalence between two invertibility statements,
and it carries no `@[stacks 073K]` attribute.  The existing part-(2) carrier
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase` is untouched.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] enoughInjectives_modules

/-- The standard derived category of the `𝒪`-modules of an algebraic space, pinned so that it is
the witness instance search produces.  `HasDerivedCategory` is data, so the statements composed
here are only composable against the witness they were elaborated with. -/
local instance degreewiseBaseChangeHasDerivedCategory (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS F hF) :=
  HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)
    [PreservesFiniteLimits (modulePullback B S hS g)]
    [PreservesFiniteColimits (modulePullback B S hS g)]

/-- **The base change map of Stacks 0736 in degree `i`**:  the morphism

`g^*H^i(Rf_*M) ⟶ H^i(Rf'_*((g')^*M))`

of `𝒪_{Y'}`-modules obtained from
`AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap` by taking degree-`i` cohomology and
rewriting the source by the comparison of the derived inverse image along the exact `g^*` with
cohomology, `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`.

`isIso_toposModuleHomologyBaseChangeMap_iff` says that invertibility of these for all `i` is
invertibility of the base change map of `D⁺`. -/
def toposModuleHomologyBaseChangeMap (comm : g' ≫ f = f' ≫ g) (i : ℤ)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2)) :
    (modulePullback B S hS g).obj
        ((DerivedCategory.Plus.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
          ((toposModulePushforward f).rightDerivedFunctorPlus.obj M)) ⟶
      (DerivedCategory.Plus.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).obj
        ((toposModulePushforward f').rightDerivedFunctorPlus.obj
          ((modulePullback B S hS g').rightDerivedFunctorPlus.obj M)) :=
  (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (modulePullback B S hS g) i).inv.app
      ((toposModulePushforward f).rightDerivedFunctorPlus.obj M) ≫
    (DerivedCategory.Plus.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).map
      ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M)

/-- **The base change map of Stacks 0736 is invertible in every degree exactly when it is
invertible in `D⁺`.**

A morphism of the bounded below derived category is invertible exactly when all of its cohomology
maps are (`CategoryTheory.DerivedCategory.Plus.isIso_iff`), and the degreewise map differs from
the degree-`i` cohomology map only by the comparison isomorphism of the derived inverse image with
cohomology. -/
theorem isIso_toposModuleHomologyBaseChangeMap_iff (comm : g' ≫ f = f' ≫ g)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2)) :
    (∀ i : ℤ, IsIso (toposModuleHomologyBaseChangeMap f g f' g' comm i M)) ↔
      IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M) := by
  rw [DerivedCategory.Plus.isIso_iff]
  refine forall_congr' fun i => ?_
  exact isIso_comp_left_iff _ _

/-- **Stacks 073K, part (1) in each degree follows from part (1) in `D⁺`.**  If the base change
map of **Stacks 0736** is invertible as a morphism of `D⁺(𝒪_{Y'})` at `M`, then the degreewise
base change map is invertible in every degree.

This is the direction the source's clause (1) consumes; it asserts nothing about invertibility
itself. -/
theorem isIso_toposModuleHomologyBaseChangeMap (comm : g' ≫ f = f' ≫ g)
    (M : DerivedCategory.Plus (Modules.{u, u} B S hS X.1 X.2))
    (hM : IsIso ((toposModuleDerivedBaseChangeMap f g f' g' comm).app M)) (i : ℤ) :
    IsIso (toposModuleHomologyBaseChangeMap f g f' g' comm i M) :=
  (isIso_toposModuleHomologyBaseChangeMap_iff f g f' g' comm M).2 hM i

end AlgebraicGeometry.Space

end
