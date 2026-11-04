module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.CoherentTwoOutOfThree.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemHom

/-!
# `D^b_{Coh}(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`

`AlgebraicGeometry.boundedCoherentDerived X` is the property of an object of `D(𝒪_X)` of being
cohomologically bounded with coherent cohomology sheaves, and
`AlgebraicGeometry.BoundedCoherentDerived X` is the full subcategory it cuts out. This file
records that the full subcategory is triangulated, in the form instance search can use.

`DerivedCategoryB.isTriangulated_derivedCategoryBBounded` says that `D^b_B(A)` is a triangulated
subcategory of `D(A)` whenever `B` is a weak Serre class, and
`Stacks.AlgebraicGeometry.CoherentTwoOutOfThree.isWeakSerreClass_isCoherent` says that coherence
is such a class on `X.Modules`, which is [Stacks, Tag 01BY] (5). Both were already proved; what
was missing is the instance putting them together, and the import that brings the second into
scope where the extension-by-zero material can see it — neither
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemHom` nor its
dependencies import either one.

## Why the weak Serre class has to be restated at `X.Modules` at all

`AlgebraicGeometry.Scheme.Modules` is a `def`, not an `abbrev`, so `X.Modules` is
*definitionally* but not *reducibly* `SheafOfModules X.ringCatSheaf`. Instance search does not
unfold a semireducible definition, so [Stacks, Tag 01BY] (5) as proved for `SheafOfModules R`
cannot be found from a goal phrased for `X.Modules`; the symptom is that
`ObjectProperty.IsWeakSerreClass (fun M : X.Modules => M.IsCoherent)` fails to synthesize, and
with it `(boundedCoherentDerived X).IsTriangulated`, `Pretriangulated` and `HasZeroObject` on
`BoundedCoherentDerived X`. The restatement at `X.Modules` is what
`Stacks.AlgebraicGeometry.CoherentTwoOutOfThree.isWeakSerreClass_isCoherent` already does.

## Which derived category this is about

There are two `HasDerivedCategory` instances available for `X.Modules`, and they are different
categories:

* `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, a global instance, whose own
  documentation records that it and not `HasDerivedCategory.standard` is the derived category
  against which the direct-sum and Brown-representability statements about `D(𝒪_X)` have content;
* `HasDerivedCategory.standard`, the localization in the larger universe, which the
  extension-by-zero material installs as a *local* instance.

So `boundedCoherentDerived X` denotes different things depending on which of the two is ambient.
The instance below is stated with `HasDerivedCategory.standard` ambient, matching
`DeligneSystemHom` and everything built on it, and it is deliberately not generalized over the
choice: one instance covering both would be a way to prove a true statement about the other
category by accident. A reader using this instance is working in the standard derived category.

## Main results

* `AlgebraicGeometry.isTriangulated_boundedCoherentDerived`: `D^b_{Coh}(𝒪_X)` is a triangulated
  subcategory of `D(𝒪_X)`, whence `BoundedCoherentDerived X` is pretriangulated.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **`D^b_{Coh}(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`.** The objects of `D(𝒪_X)` that
are cohomologically bounded with coherent cohomology sheaves are closed under the operations of
the triangulated structure, so the full subcategory
`AlgebraicGeometry.BoundedCoherentDerived X` is pretriangulated.

This is `DerivedCategoryB.isTriangulated_derivedCategoryBBounded` for the weak Serre class of
coherent sheaves of modules, [Stacks, Tag 01BY] (5), which
`Stacks.AlgebraicGeometry.CoherentTwoOutOfThree.isWeakSerreClass_isCoherent` supplies.

The derived category here is the one for `HasDerivedCategory.standard`; see the note in the
module documentation on why that choice is pinned rather than quantified over. -/
public instance isTriangulated_boundedCoherentDerived (X : Scheme.{u}) :
    (boundedCoherentDerived X).IsTriangulated :=
  DerivedCategoryB.isTriangulated_derivedCategoryBBounded _

end AlgebraicGeometry

end
