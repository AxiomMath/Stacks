module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare

/-!
# Functoriality of the naive cotangent complex on a topological space

A commutative square
```
B ──β──▸ B'
▲         ▲
a         a'
│         │
A ──f──▸ A'
```
of sheaves of commutative rings on a topological space `X` induces a canonical `B`-linear map
of complexes `NL_{B/A} ⟶ NL_{B'/A'}`.  This is the construction for the site of opens of `X`.

## Main definitions

* `Stacks.SheafOfModules.spaceNaiveCotangentComplexMapOfSquare`: the chain map
  `NL_{B/A} ⟶ NL_{B'/A'}` of complexes of sheaves of modules on `X`.

## Main results

* `Stacks.SheafOfModules.spaceNaiveCotangentComplexMapOfSquare_f_negOne` and
  `Stacks.SheafOfModules.spaceNaiveCotangentComplexMapOfSquare_f_zero`: its two nonzero
  components are the map of conormal sheaves and the map of the scalar extensions of the
  relative differentials.
* `Stacks.SheafOfModules.spaceNaiveCotangentComplexMapOfSquare_comp`: the chain map is compatible
  with compositions, that is, for two squares side by side the composite
  `NL_{B/A} ⟶ NL_{B'/A'} ⟶ NL_{B''/A''}` is the chain map of the outer rectangle.

## Implementation notes

Everything is the site-level construction of
`StacksFrontier/CategoryTheory/Sites/Modules/InternalHomAndFlatness/NaiveCotangentSquare.lean`
instantiated at `Opens.grothendieckTopology X`, in the universe pattern
`naiveCotangentComplex.{u, u, u, u}` used for the naive cotangent complex of sheaves of rings on
a space elsewhere in `StacksFrontier/Topology/Sheaves/Modules/`.  The sheaves are written as
objects of `CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat`, not of
`TopCat.Sheaf`: the two category structures are definitionally equal but only the first is the
one the site-level development composes in.

## References

* [Stacks Project, Tag 08TK](https://stacks.math.columbia.edu/tag/08TK)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the same construction
  on an arbitrary site.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {X : TopCat.{u}}
  (A A' B B' : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) (a' : A' ⟶ B') (f : A ⟶ A') (β : B ⟶ B') (hsq : a ≫ β = f ≫ a')

include hsq in
/-- **Stacks 08TK.** The canonical `B`-linear chain map `NL_{B/A} ⟶ NL_{B'/A'}` attached to a
commutative square of sheaves of commutative rings on a topological space. -/
@[stacks 08TK "the canonical B-linear map of complexes NL_{B/A} ⟶ NL_{B'/A'}"]
noncomputable def spaceNaiveCotangentComplexMapOfSquare :
    naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a ⟶
      ((_root_.SheafOfModules.restrictScalars.{u, u, u, u} (underlyingRingHomOfSite.{u, u, u} β)
        ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A' B' a') :=
  naiveCotangentComplexMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X) A B a A' B' a'
    f β hsq

include hsq in
/-- In degree `-1` the chain map is the map of conormal sheaves. -/
theorem spaceNaiveCotangentComplexMapOfSquare_f_negOne :
    (spaceNaiveCotangentComplexMapOfSquare A A' B B' a a' f β hsq).f (-1) =
      eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology X) A B a) ≫
        naiveCotangentConormalMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X)
            A B a A' B' a' f β hsq ≫
          (_root_.SheafOfModules.restrictScalars.{u, u, u, u}
              (underlyingRingHomOfSite.{u, u, u} β)).map
            (eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
              (Opens.grothendieckTopology X) A' B' a').symm) :=
  naiveCotangentComplexMapOfSquare_f_negOne.{u, u, u, u} (Opens.grothendieckTopology X)
    A B a A' B' a' f β hsq

include hsq in
/-- In degree `0` the chain map is the map on the scalar extensions of the differentials. -/
theorem spaceNaiveCotangentComplexMapOfSquare_f_zero :
    (spaceNaiveCotangentComplexMapOfSquare A A' B B' a a' f β hsq).f 0 =
      eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology X) A B a) ≫
        naiveCotangentTensorMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X)
            A B a A' B' a' f β hsq ≫
          (_root_.SheafOfModules.restrictScalars.{u, u, u, u}
              (underlyingRingHomOfSite.{u, u, u} β)).map
            (eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
              (Opens.grothendieckTopology X) A' B' a').symm) :=
  naiveCotangentComplexMapOfSquare_f_zero.{u, u, u, u} (Opens.grothendieckTopology X)
    A B a A' B' a' f β hsq

section Comp

variable (A'' B'' : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a'' : A'' ⟶ B'') (f' : A' ⟶ A'') (β' : B' ⟶ B'') (hsq' : a' ≫ β' = f' ≫ a'')

include hsq hsq' in
/-- **Stacks 08TK.** The canonical chain map attached to a commutative square of sheaves of
commutative rings on a topological space is compatible with compositions: given a commutative
diagram
```
B ──β──▸ B' ──β'──▸ B''
▲         ▲          ▲
a         a'         a''
│         │          │
A ──f──▸ A' ──f'──▸ A''
```
the composition `NL_{B/A} ⟶ NL_{B'/A'} ⟶ NL_{B''/A''}` is the map attached to the outer
rectangle. -/
@[stacks 08TK "compatibility of the canonical map of complexes with compositions"]
theorem spaceNaiveCotangentComplexMapOfSquare_comp :
    spaceNaiveCotangentComplexMapOfSquare A A' B B' a a' f β hsq ≫
        ((_root_.SheafOfModules.restrictScalars.{u, u, u, u}
            (underlyingRingHomOfSite.{u, u, u} β)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (spaceNaiveCotangentComplexMapOfSquare A' A'' B' B'' a' a'' f' β' hsq') =
      spaceNaiveCotangentComplexMapOfSquare A A'' B B'' a a'' (f ≫ f') (β ≫ β')
        (square_comp hsq hsq') :=
  naiveCotangentComplexMapOfSquare_comp.{u, u, u, u} (Opens.grothendieckTopology X)
    A B a A' B' a' f β hsq A'' B'' a'' f' β' hsq'

end Comp

end Stacks.SheafOfModules
