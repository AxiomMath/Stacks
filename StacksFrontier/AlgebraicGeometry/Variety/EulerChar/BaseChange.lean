module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.Tactic.StacksAttribute

/-!
# The base-change diagram

This file packages a cartesian square of schemes together with a quasi-coherent module on its
upper-right corner.  The module on the upper-left corner is its inverse image, and the two lower
objects associated to the diagram are the corresponding total derived direct images.

## Main definitions

* `AlgebraicGeometry.BaseChangeDiagram` is the cartesian square and quasi-coherent module
  occurring in the base-change diagram.
* `AlgebraicGeometry.BaseChangeDiagram.pulledBack` is the module denoted by `𝓕'` in the diagram.
* `AlgebraicGeometry.BaseChangeDiagram.derivedPushforward` and
  `AlgebraicGeometry.BaseChangeDiagram.derivedPushforward'` are the objects denoted by `Rf_*𝓕`
  and `Rf'_*𝓕'`.

## Main results

The structure, together with its canonical constructions, records the entire diagram.

## Implementation notes

The equality `𝓕' = (g')^*𝓕` is made definitional rather than replacing it by a noncanonical
choice of an isomorphic module.  Total derived direct images are formed in the bounded-below
derived categories, after placing a module in degree zero.

## References

* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 02KF.** The base-change diagram: a cartesian square of schemes,
together with the quasi-coherent module `𝓕` on `X`. -/
@[stacks 02KF "the cartesian square and quasi-coherent module"]
structure BaseChangeDiagram where
  X' : Scheme.{u}
  X : Scheme.{u}
  S' : Scheme.{u}
  S : Scheme.{u}
  g' : X' ⟶ X
  f' : X' ⟶ S'
  f : X ⟶ S
  g : S' ⟶ S
  isPullback : IsPullback g' f' f g
  F : X.Modules
  [isQuasicoherent : F.IsQuasicoherent]

namespace BaseChangeDiagram

/-- The module `𝓕' = (g')^*𝓕` in the base-change diagram. -/
@[stacks 02KF "the pulled-back module"]
noncomputable abbrev pulledBack (d : BaseChangeDiagram) : d.X'.Modules :=
  (Scheme.Modules.pullback d.g').obj d.F

/-- The total derived direct image `Rf_*𝓕` in the base-change diagram. -/
@[stacks 02KF "the lower-right derived direct image"]
noncomputable abbrev derivedPushforward (d : BaseChangeDiagram) :
    DerivedCategory.Plus d.S.Modules :=
  (Scheme.Modules.pushforward d.f).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor d.X.Modules 0).obj d.F)

/-- The total derived direct image `Rf'_*𝓕'` in the base-change diagram. -/
@[stacks 02KF "the lower-left derived direct image"]
noncomputable abbrev derivedPushforward' (d : BaseChangeDiagram) :
    DerivedCategory.Plus d.S'.Modules :=
  (Scheme.Modules.pushforward d.f').rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor d.X'.Modules 0).obj d.pulledBack)

end BaseChangeDiagram

end AlgebraicGeometry
