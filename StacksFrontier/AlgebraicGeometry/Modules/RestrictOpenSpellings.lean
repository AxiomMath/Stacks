module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestrictOpen
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# The four spellings of restriction to an open agree

Restriction of sheaves of modules to an open is constructed four times in this repository, each
time as a pushforward along the open-image functor of sites with the identity change of scalars,
and no two of them are interchangeable to instance search:

* `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι` — Mathlib's, along the open immersion of
  schemes. This is the one the transitivity sequence is restricted by, so it is where a splitting
  of the restricted sequence lives
  (`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsShortComplexRestrict`).
* `AlgebraicGeometry.SheafOfModules.siteRestrict` — along the open-image functor of the
  restricted *ringed space*.
* `Stacks.Cohomology.HigherDirectImage.moduleRestriction` — along the open-image functor of the
  open subset. This is the one the tensor product crosses
  (`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso` and its naturality).
* `SheafOfModules.overFunctor U ⋙ (TopologicalSpace.Opens.sheafOfModulesEquivOver _).functor` —
  the slice site followed by the transport to the open subspace. This is the one the exterior
  algebra crosses, with its algebra structure
  (`SheafOfModules.exteriorRestrictOpenSubspaceIso`).

**Nothing here is new mathematics and almost nothing here is new Lean.** The two nontrivial legs
were already present and already proved —
`AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict`
and `AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor` — and the third leg is
`rfl`. This file records that, and composes them once, so that a crossing proved against one
spelling can be used against another without each consumer rediscovering the chain.

## Main results

* `Stacks.SheafOfModules.RestrictOpen.siteRestrict_eq_moduleRestriction`: the ringed-space
  spelling and the open-subset spelling are **the same functor**, not merely isomorphic. Both are
  `SheafOfModules.pushforward` of the identity along the same functor on opens.
* `Stacks.SheafOfModules.RestrictOpen.overFunctorIsoRestrictFunctor`: **the slice site followed
  by the transport to the open subspace is Mathlib's restriction along the open immersion.** This
  is the chain in the direction it is needed: a statement about `(-).over U` carried to a
  statement about `Scheme.Modules.restrictFunctor U.ι`.

## Implementation notes

**Why there is no `moduleRestriction ≅ Scheme.Modules.restrictFunctor` declaration here.**
`AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor` already has that type: its
source `StrictlyPerfect.restrictModules X.toRingedSpace U` is `moduleRestriction X.toRingedSpace U`
definitionally, so the existing declaration applies at the `moduleRestriction` spelling with
nothing to transport, and a second declaration would be a copy of it under another name. The
composite below is the only genuinely new arrow.

## References

* [Stacks Project, Tag 01AD](https://stacks.math.columbia.edu/tag/01AD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.SheafOfModules.RestrictOpen

/-- **Restriction to an open of a ringed space and restriction to the open subset are the same
functor.** `AlgebraicGeometry.SheafOfModules.siteRestrict` pushes forward along the open-image
functor of the inclusion of the restricted ringed space and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` along the open-image functor of the open
subset; those are the same functor on opens, and both changes of scalars are the identity, so the
two agree on the nose. -/
theorem siteRestrict_eq_moduleRestriction (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    AlgebraicGeometry.SheafOfModules.siteRestrict X U = moduleRestriction X U :=
  rfl

/-- **The slice site, transported to the open subspace, is Mathlib's restriction along the open
immersion.** The first leg is
`AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict` and the second is
`AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor`, which applies at the
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` spelling because
`Stacks.SheafOfModules.RestrictOpen.siteRestrict_eq_moduleRestriction` is `rfl`.

This is what carries a crossing proved for `(-).over U` — the exterior algebra of
`SheafOfModules.exteriorRestrictOpenSubspaceIso`, say — to the functor that a splitting of a
restricted short complex of `𝒪_X`-modules is stated against. -/
def overFunctorIsoRestrictFunctor (X : Scheme.{u}) (U : X.Opens) :
    _root_.SheafOfModules.overFunctor (structureSheafRing X.toRingedSpace) U ⋙
        (U.sheafOfModulesEquivOver (structureSheafRing X.toRingedSpace)).functor ≅
      Scheme.Modules.restrictFunctor U.ι :=
  AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict X.toRingedSpace U ≪≫
    AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor X U

end Stacks.SheafOfModules.RestrictOpen

end
