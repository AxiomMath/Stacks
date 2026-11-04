module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexAlgebraOpenSubspace
import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a K-injective complex to an open subspace

Let `(X, O_X)` be a ringed space, let `U ⊆ X` be open and let `Q` be a complex of
`O_X`-modules. `Stacks.SheafOfModules.openSubspaceRestrictComplex` is its restriction read on the
ringed space `X.restrict U`: the restriction to the slice site `Opens X / U` followed by the
transport off that site along `Stacks.SheafOfModules.openSubspaceEquiv`. This file shows that the
restriction of a K-injective complex in that spelling is K-injective.

The slice half is Stacks 08FI, `Stacks.Cohomology.Localization.isKInjective_over`. The transport
half is the adjoint criterion of Stacks 08BJ,
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`, applied to an *equivalence*: it is
both adjoints of itself and exact, so it carries K-injective complexes to K-injective complexes.

## Main results

* `Stacks.SheafOfModules.isKInjective_openSubspacePushComplex`: the transport of a complex off the
  slice site onto the open subspace preserves K-injectivity.
* `Stacks.SheafOfModules.isKInjective_openSubspaceRestrictComplex`: the restriction of a
  K-injective complex of `O_X`-modules, read on `X.restrict U`, is K-injective.

## Implementation notes

**The two conclusions are theorems, not instances, and their hypotheses are explicit.** The sheaf
of rings of the slice has two spellings here — `((ringedSite X.sheaf).over U).ringSheaf`, which
`Stacks.SheafOfModules.openSubspacePushComplex` and
`AlgebraicGeometry.RingedSite.restrictComplex` produce, and `(structureSheafRing X).over U`, which
`Stacks.SheafOfModules.openSubspaceEquiv` produces. The two are equal, and *elaboration* crosses
the equality, but `structureSheafRing` is a plain definition, so **instance
search does not**: stated as instances with instance-implicit hypotheses, these two would be
unusable, the hypothesis being available only at the other spelling. With the hypotheses explicit
a consumer introduces each with `letI` at whichever spelling it holds, and the ascription is
checked at default transparency, where the two agree. The proofs do exactly that, naming the
complex once at each spelling.

This is the same hazard as the one recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientRingSheafOpenSubspaceIdeal`, where the two
spellings of a sheaf of rings on the slice are `sheafCompose` after `overPullback` and
`overPullback` after `sheafCompose`, and the resolution there is the same: route through one
spelling and never let instance search cross.

**Why an equivalence needs no separate argument.** `CategoryTheory.Equivalence.inverse_additive`
makes the inverse of an additive equivalence additive, an equivalence preserves all limits and
colimits, and `Equivalence.symm.toAdjunction` exhibits the forward functor as the right adjoint of
the inverse. So `CochainComplex.isKInjective_mapHomologicalComplex_of_exact` applies with nothing
to check. The packaged form of that specialisation,
`CochainComplex.isKInjective_mapHomologicalComplex_of_equivalence`, is already in the library,
in `StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.ChaoticRingedSites`; the adjoint
criterion is cited directly here rather than importing that module, which is about a different
subject and would carry its whole subtree into this one.

## References

* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe v u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- The forward functor of the open-subspace equivalence is additive: it is the pushforward along
the structure map of the equivalence of ringed sites
(`Stacks.SheafOfModules.pushforward_openSubspacePhi`), which is additive. -/
instance additive_openSubspaceEquiv_functor : (openSubspaceEquiv U).functor.Additive :=
  inferInstanceAs (_root_.SheafOfModules.pushforward.{u} (openSubspacePhi U)).Additive

/-- **The transport of complexes off the slice site onto the open subspace preserves
K-injectivity.** `Stacks.SheafOfModules.openSubspacePushComplex` is the degreewise image under
`Stacks.SheafOfModules.openSubspaceEquiv`, an equivalence, so this is
`CochainComplex.isKInjective_mapHomologicalComplex_of_equivalence`. The hypothesis is explicit
because it is held at the other of the two spellings of the sheaf of rings of the slice — see the
implementation notes. -/
theorem isKInjective_openSubspacePushComplex
    (I : CochainComplex
      (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite X.sheaf).over U).O)) ℤ)
    (hI : I.IsKInjective) :
    ((openSubspacePushComplex U).obj I).IsKInjective :=
  let I' : CochainComplex (_root_.SheafOfModules.{u} ((structureSheafRing X).over U)) ℤ := I
  let : I'.IsKInjective := hI
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact (openSubspaceEquiv U).functor
    (openSubspaceEquiv U).inverse (openSubspaceEquiv U).symm.toAdjunction I'

/-- **The restriction of a K-injective complex of `O_X`-modules to an open subspace is
K-injective**, in the spelling in which it lives on the ringed space `X.restrict U`. Stacks 08FI
on the slice site, followed by the transport off it.

This is the K-injectivity the comparison of models over an open needs:
`Stacks.SheafOfModules.modelComparison` asks it of the complex it compares a strictly perfect one
with, and over an open that complex is the restriction of a resolution chosen on all of `X`. -/
theorem isKInjective_openSubspaceRestrictComplex
    (Q : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hQ : Q.IsKInjective) :
    (openSubspaceRestrictComplex U Q).IsKInjective :=
  let : Q.IsKInjective := hQ
  isKInjective_openSubspacePushComplex U _
    (Stacks.Cohomology.Localization.isKInjective_over _ _ U Q)

end Stacks.SheafOfModules

end
