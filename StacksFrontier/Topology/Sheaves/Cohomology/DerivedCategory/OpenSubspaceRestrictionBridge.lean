module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingObjectTransport
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictKInjective
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictRestrictComp

/-!
# The restriction displayed by a system is restriction inside the open subspace

Let `(X, 𝒪_X)` be a ringed space, let `O` be an open subset and let `W ≤ O` be a smaller open.
Situation 0D67 displays a restriction functor `Stacks.DerivedGlueing.LocallyGiven.restriction`
from the objects over `O` to the objects over `W`, built — through
`Stacks.DerivedGlueing.openModuleRestriction` — by extending by zero along `O` to the whole of
`X` and restricting to `W`.  The Stacks Project's own proofs of [Stacks, Tag 0D68] and
[Stacks, Tag 0D6C] instead form the induced system *on the ringed space `O`* and work there.

This file identifies the two readings at the level of sheaves of modules.  The ringed space of
the open `O` is Mathlib's `AlgebraicGeometry.SheafedSpace.restrict`, and the first four results
below record that no translation at all is needed to name the objects: the structure sheaf of
rings of `X|O` *is* `Stacks.DerivedGlueing.restrictedRingSheaf X O`, so
`Stacks.DerivedGlueing.OpenDerivedCategory X O` is the unbounded derived category of modules on
the ringed space `X|O`, and restriction of modules to an open subspace,
`AlgebraicGeometry.RingedSpace.restrictModules`, is `ExtensionByZeroModules.jStar` — which is
`AlgebraicGeometry.RingedSpace.restrictModules_eq_jStar`.

The content is `Stacks.DerivedGlueing.openModuleRestrictionIsoSubspace`: restriction from `O` to
`W` is restriction inside `X|O` to the open of `X|O` corresponding to `W`, followed by the
comparison `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare` of the doubly restricted
space `(X|O)|W'` with the singly restricted space `X|W`.  The two inputs are
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleRestrictIso`, which says that double
restriction followed by the comparison is single restriction, and
`Stacks.DerivedGlueing.jShriekUnitIso`, which says that restricting to `O` an extension by zero
along `O` is the identity — the step that cancels the extension by zero that
`Stacks.DerivedGlueing.openModuleRestriction` begins with.

## Main results

* `Stacks.DerivedGlueing.structureSheafRing_restrict` and
  `Stacks.DerivedGlueing.underlyingRingSheaf_restrict`: the structure sheaf of rings of the open
  subspace is the restricted ring sheaf of Situation 0D67.
* `Stacks.DerivedGlueing.openModuleRestrictionIsoSubspace` and
  `Stacks.DerivedGlueing.openModuleRestrictionIsoJStarCompare`: the identification itself, in the
  two spellings of restriction to an open subspace.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpace (restrictModules)
open AlgebraicGeometry.RingedSpace.CorrespondingOpens (ofBase)

namespace Stacks.DerivedGlueing

universe u

variable {X : RingedSpace.{u, u}}

/-! ### The open subspace carries the modules of Situation 0D67 -/

/-- **The structure sheaf of rings of the open subspace `X|U` is the restricted ring sheaf.**
Both are the presheaf of rings of `X` precomposed with the inclusion of the opens of `U` into
the opens of `X`, so there is nothing to prove. -/
public theorem structureSheafRing_restrict (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    structureSheafRing (X.restrict U.isOpenEmbedding) = restrictedRingSheaf X U := rfl

/-- **The same, for the spelling used by Situation 0D67.** -/
public theorem underlyingRingSheaf_restrict (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    underlyingRingSheaf (X.restrict U.isOpenEmbedding) = restrictedRingSheaf X U := rfl

/-- **The objects over an open are the objects of the derived category of the open subspace.**
`Stacks.DerivedGlueing.OpenDerivedCategory X U` is the unbounded derived category of modules
over `Stacks.DerivedGlueing.restrictedRingSheaf X U`, and that is the structure sheaf of rings
of `X|U`; so an object given over `U` in Situation 0D67 is a *global* object on the ringed
space `X|U`, with no comparison interposed. -/
public theorem moduleSheaves_restrict (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)) =
      SheafOfModules.{u} (restrictedRingSheaf X U) := rfl

/-! ### Restriction from an open to a smaller one, read inside the open subspace -/

/-- **The restriction of Situation 0D67 from `O` to `W` is restriction inside the ringed space
`X|O`.** On sheaves of modules, `Stacks.DerivedGlueing.openModuleRestriction X W O` — extend by
zero along `O`, then restrict to `W` — is restriction to the open of `X|O` corresponding to `W`,
followed by the comparison of `(X|O)|W'` with `X|W`.

The extension by zero that `Stacks.DerivedGlueing.openModuleRestriction` begins with is cancelled
by restriction to `O`, which is `Stacks.DerivedGlueing.jShriekUnitIso`; what is left is double
restriction, and
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleRestrictIso` identifies that, after the
comparison, with single restriction to `W`. -/
public def openModuleRestrictionIsoSubspace {O W : Opens X.carrier} (hWO : W ≤ O) :
    openModuleRestriction X W O hWO ≅
      restrictModules.{u, u} (X.restrict O.isOpenEmbedding) (ofBase hWO).sub ⋙
        (ofBase hWO).compare :=
  Functor.isoWhiskerLeft (jShriek O (underlyingRingSheaf X))
      (AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleRestrictIso (ofBase hWO)).symm ≪≫
    Functor.isoWhiskerRight (jShriekUnitIso O).symm
      (restrictModules.{u, u} (X.restrict O.isOpenEmbedding) (ofBase hWO).sub ⋙
        (ofBase hWO).compare) ≪≫
    (restrictModules.{u, u} (X.restrict O.isOpenEmbedding) (ofBase hWO).sub ⋙
      (ofBase hWO).compare).leftUnitor

/-- **The same identification, with restriction to the open subspace spelled as `j^*`.** This is
the spelling in which Situation 0D67's own restriction functors are written, and the one under
which the instances of `ExtensionByZeroModules.jStar` apply. -/
public def openModuleRestrictionIsoJStarCompare {O W : Opens X.carrier} (hWO : W ≤ O) :
    openModuleRestriction X W O hWO ≅
      jStar (ofBase hWO).sub (underlyingRingSheaf (X.restrict O.isOpenEmbedding)) ⋙
        (ofBase hWO).compare :=
  openModuleRestrictionIsoSubspace hWO ≪≫
    eqToIso (congrArg (fun F => F ⋙ (ofBase hWO).compare)
      (AlgebraicGeometry.RingedSpace.restrictModules_eq_jStar
        (X.restrict O.isOpenEmbedding) (ofBase hWO).sub))

end Stacks.DerivedGlueing

end
