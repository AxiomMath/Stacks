module

public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonExactFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModelIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme

/-!
# Being a dualizing complex transports between the models of `D(𝒪_X)`

`CategoryTheory.HasDerivedCategory.{w} X.Modules` is a *chosen* localization of the cochain
complexes of `𝒪_X`-modules at the quasi-isomorphisms, and this repository works with two such
choices: the standard one `CategoryTheory.HasDerivedCategory.standard`, and the locally small one
of [Stacks, Tag 079Q] which `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` installs as a
global instance. The objects of the two models are literally the same type, but their morphisms
live in different universes, so `Stacks.Duality.IsDualizingComplex` read at one of them is a
*different predicate* from the same expression read at the other — and which one a statement
means is decided by instance resolution, invisibly.

This file is the comparison. `Stacks.Duality.HasDualizingModelOn` mentions the ambient model only
through restriction to an affine open, which is an exact functor; and an exact functor commutes
with the model comparison `StacksDraft.DerivedModel.modelEquiv` by
`StacksDraft.DerivedModel.modelEquivCompMapDerivedCategoryIso`. Since the predicate depends on
that restriction only up to isomorphism, it transports.

## Main results

All in the namespace `Stacks.Duality`.

* `hasDualizingModelOn_modelEquiv_iff` — carrying a dualizing model at an affine open is the same
  condition at the two models, read across `StacksDraft.DerivedModel.modelEquiv`.
* `isDualizingComplex_modelEquiv_iff` — hence being a dualizing complex is, the condition being a
  conjunction over affine opens of the previous one.
* `isDualizingComplex_standard_iff_locallySmall` and the two implications
  `IsDualizingComplex.standard_of_locallySmall`, `IsDualizingComplex.locallySmall_of_standard` —
  the specialisation to the two models this repository actually uses, which is the form a caller
  wants: the locally small model is what bare instance resolution picks, and the standard model is
  what the derived internal hom of [Stacks, Tag 08DI] and the duality statements of
  [Stacks, Section 0AU3] are stated at.

## Implementation notes

*No `@[stacks]` attribute is placed on anything in this file, and no tag's coverage changes.* A
comparison of two readings of one predicate is repository bookkeeping, not a statement of the
Stacks Project: the mathematical content of [Stacks, Tag 0A87] is in
`Stacks.Duality.IsDualizingComplex` itself, and transporting it along an equivalence of two chosen
localizations adds nothing to it.

Nothing here is proved by `rfl`, and that is the point of the file rather than an accident: the
two readings of `Stacks.Duality.HasDualizingModelOn` are *not* definitionally equal — the
restriction functors they are built from are `CategoryTheory.Functor.mapDerivedCategory` at
different source models, and those are different terms. Checked directly: a `rfl` proof of the
equality of the two predicates, of the two readings of `Stacks.Duality.IsDualizingComplex`, and of
the two readings of `Stacks.Duality.quasiCoherentDerivedCategory` is rejected in each case. What
*is* true by `rfl` is only that the two models have the same type of objects.

The model of `D(𝒪_X)` is written into every statement below with `@` rather than fixed by a local
instance attribute, as `Duality/UpperShriekChartModelComparison.lean` does and for the same
reason: which model each side is read at is exactly the content, and an attribute in the file
header would hide it.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w z

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-! ### The two models this repository uses

The general two-model comparison is already in the library and is deliberately **not** restated
here: `Stacks.Duality.hasDualizingModelOn_modelEquiv_iff` and
`Stacks.Duality.isDualizingComplex_modelEquiv_iff` live in
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModelIndependence`,
which this module imports. What is added here is only the specialisation to the pair of models
this development actually works with. -/

/-- **Being a dualizing complex at the standard model is being one at the locally small model,
across the comparison.** This is `Stacks.Duality.isDualizingComplex_modelEquiv_iff` at the pair of
models the development actually works with: `CategoryTheory.HasDerivedCategory.standard`, which
the derived internal hom of [Stacks, Tag 08DI] and the duality statements of
[Stacks, Section 0AU3] are stated at, and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
[Stacks, Tag 079Q], which is a global instance and so the one bare instance resolution picks.

The comparison is `AlgebraicGeometry.Scheme.Modules.derivedModelEquiv`, which is by definition
`StacksDraft.DerivedModel.modelEquiv` at this pair, so this statement composes with the other
bridges phrased through it — in particular with
`StacksDraft.DerivedModel.schemeDerivedPushforwardStandardIso` for `Rf_*`. -/
theorem isDualizingComplex_standard_iff_locallySmall
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) :
    @IsDualizingComplex X _ (HasDerivedCategory.standard _) K ↔
      IsDualizingComplex ((Scheme.Modules.derivedModelEquiv X).functor.obj K) :=
  (isDualizingComplex_modelEquiv_iff _ _ K).symm

/-- The locally small reading implies the standard one, the direction a caller needs when a
result proved by bare instance resolution has to be fed to a statement at the standard model. -/
theorem IsDualizingComplex.standard_of_locallySmall
    {K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    (h : IsDualizingComplex ((Scheme.Modules.derivedModelEquiv X).functor.obj K)) :
    @IsDualizingComplex X _ (HasDerivedCategory.standard _) K :=
  (isDualizingComplex_standard_iff_locallySmall K).2 h

/-- The standard reading implies the locally small one. -/
theorem IsDualizingComplex.locallySmall_of_standard
    {K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    (h : @IsDualizingComplex X _ (HasDerivedCategory.standard _) K) :
    IsDualizingComplex ((Scheme.Modules.derivedModelEquiv X).functor.obj K) :=
  (isDualizingComplex_standard_iff_locallySmall K).1 h

end Stacks.Duality

end
