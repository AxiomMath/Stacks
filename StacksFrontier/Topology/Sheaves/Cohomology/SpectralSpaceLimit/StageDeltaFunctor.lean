module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Colimit
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.PullbackAsAMorphismOfDeltaFunctors
public import StacksFrontier.Topology.Sheaves.Limits.AbelianSystemAbelian

/-!
# The stage-side δ-functor on a system of abelian sheaves, and exactness of its colimits

The degree induction of [Stacks, Tag 0A37] (Lemma 20.19.3) runs the comparison of
`CategoryTheory.DeltaFunctor.isIso_app_of_isIso_app_zero'` on the abelian category of systems
`SpectralDiagram.AbelianSystem`. This file imports what instance search needs to find the
exactness of filtered colimits that comparison uses, and records the stage-side δ-functor at one
stage.

## Exactness of filtered colimits of abelian groups

Mathlib has `CategoryTheory.AB5 AddCommGrpCat` (`Mathlib/Algebra/Category/Grp/AB.lean`) and
`CategoryTheory.AB5OfSize.ofShape` reads off any filtered shape; `(Over i)ᵒᵖ` is filtered for a
cofiltered index category by `CategoryTheory.IsCofiltered.over` together with
`CategoryTheory.isFiltered_op_of_isCofiltered`; and the sheaf-category analogue follows from
Mathlib's `CategoryTheory.Sheaf.hasExactColimitsOfShape`. All of it is instance synthesis once
`Mathlib.Algebra.Category.Grp.AB` and `Mathlib.CategoryTheory.Filtered.Final` are imported, and
this file imports both.

## The stage-side functor at the site spelling

The stage side precomposes `Stacks.Cohomology.AbelianColimit.H'deltaFunctor` with
`SpectralDiagram.ev`. The `TopCat.Sheaf` and site spellings of the stage category are `rfl`-equal,
with `rfl`-equal `Preadditive` and `Abelian` instances, but `(D.ev j).Additive`,
`PreservesFiniteLimits (D.ev j)` and `PreservesFiniteColimits (D.ev j)` all synthesize on the nose
at the `SpectralDiagram.StageSheaf` type, and `(D.ev j).Additive` then fails to synthesize when
`D.ev j` is passed to `CategoryTheory.DeltaFunctor.precomp`, whose `Ψ : A' ⥤ A` forces the
*site*-spelled codomain — supplying the instance by name at the use site does not help, because the
ascribed term keeps its own type. A named declaration whose stated type is the one instance search
needs is `SpectralDiagram.evSite`, and with its three exactness instances the precomposition goes
through: `SpectralDiagram.stageDelta`.

## Main results

* `SpectralDiagram.evSite`: evaluation at a stage, stated at the site spelling, with
  `SpectralDiagram.evSite_additive`, `…_preservesFiniteLimits`, `…_preservesFiniteColimits`.
* `SpectralDiagram.stageDelta`: **the stage-side δ-functor on systems**, `H'deltaFunctor`
  precomposed with evaluation.

## Use

The stage side of the comparison of δ-functors of the degree induction of Stacks 0A37 is the
diagram `SpectralDiagram.AbelianSystem.stageDiagram`
(`Topology/Sheaves/Cohomology/SpectralSpaceLimit/ComparisonOfDeltaFunctors.lean`), built on the
`Ext`-δ-functors `ModuleSheafCohomology.extDeltaFunctor (evSite D j) (freeOfOpen U)`; its colimit
is formed with the colimit-exactness instances that this file's imports make available.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

universe u

namespace SpectralDiagram

variable {J : Type u} [SmallCategory J] [IsCofiltered J] (D : SpectralDiagram.{u, u} J)

/-- **Evaluation of a system at a stage, stated at the site spelling of the category of abelian
sheaves.** This is `SpectralDiagram.ev` and nothing else — `SpectralDiagram.StageSheaf j` and
`CategoryTheory.Sheaf (TopologicalSpace.Opens.grothendieckTopology ↥(D.F.obj j)) AddCommGrpCat`
are `rfl`-equal, with `rfl`-equal `Preadditive` and `Abelian` instances. What the named
declaration buys is that its *stated* type is the one instance search uses when the functor is
handed to `CategoryTheory.DeltaFunctor.precomp`: at the `StageSheaf` spelling the three exactness
instances are found, and at the site spelling, reached by a type ascription, they are not. -/
def evSite (j : J) :
    D.AbelianSystem ⥤ Sheaf (Opens.grothendieckTopology ↥(D.F.obj j)) AddCommGrpCat.{u} :=
  D.ev j

/-- Evaluation at a stage is additive, at the site spelling. -/
instance evSite_additive (j : J) : (evSite D j).Additive :=
  SpectralDiagram.AbelianSystem.ev_additive j

/-- Evaluation at a stage is left exact, at the site spelling. -/
instance evSite_preservesFiniteLimits (j : J) : PreservesFiniteLimits (evSite D j) :=
  SpectralDiagram.AbelianSystem.ev_preservesFiniteLimits j

/-- Evaluation at a stage is right exact, at the site spelling. -/
instance evSite_preservesFiniteColimits (j : J) : PreservesFiniteColimits (evSite D j) :=
  SpectralDiagram.AbelianSystem.ev_preservesFiniteColimits j

/-- **The stage-side δ-functor of [Stacks, Tag 0A37] on the abelian category of systems**: the
cohomology δ-functor `Stacks.Cohomology.AbelianColimit.H'deltaFunctor` of an open `U` of the
`j`-th space, precomposed with evaluation at the `j`-th stage. Precomposition is legitimate
because evaluation is additive and exact in both directions
(`SpectralDiagram.evSite_additive`, `…_preservesFiniteLimits`, `…_preservesFiniteColimits`), which
is what `CategoryTheory.DeltaFunctor.precomp` asks of it.

This is the object part of the stage side of the degree induction. -/
def stageDelta (j : J) (U : Opens ↥(D.F.obj j)) :
    CategoryTheory.DeltaFunctor D.AbelianSystem AddCommGrpCat.{u} :=
  (Stacks.Cohomology.AbelianColimit.H'deltaFunctor (X := ↥(D.F.obj j)) U).precomp (evSite D j)

end SpectralDiagram

end
