module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
import StacksCore.Tactic.StacksAttribute

/-!
# The map `M ⊗^L K^∨ ⟶ RSheafHom(K, M)` at a perfect `K`

Let `(X, O_X)` be a ringed space, let `K` be a **perfect** object of `D(O_X)` and let `M` be an
arbitrary object. The third assertion of **Stacks 08DQ** is that the canonical map of
Stacks 08I1

`Φ : M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)`

(`Stacks.SheafOfModules.derivedTensorDualToSheafHom`) is an isomorphism. That is what this file
proves, with perfectness of `K` as the only hypothesis; nothing is assumed of `M`.

## Main results

* `Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`: **Stacks 08DQ, third
  assertion.**

## How it is proved

This reads off the ringed-site statement
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect` at the site of
opens of the space, for the canonical derived tensor product; the two notions of perfection agree
because the predicate used here *is* the site-level one of Stacks 08G5.

The site-level proof is in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect`, whose module
documentation sets out the argument. In outline: `Φ` is the composition morphism of Stacks 0A98
at intermediate object the structure sheaf, and invertibility of that morphism is replaced, once
and for all, by quasi-isomorphy of a morphism of *complexes* at one choice of models
(`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_of_coversTop`). Quasi-isomorphy of
a morphism of complexes is local on the site, so no compatibility of the *derived* morphism with
restriction to a slice is needed — the library has none — and the condition may be checked over
the members of the covering that perfectness supplies. Over such a member the source acquires a
strictly perfect model, where the morphism is handled by the restriction square
`AlgebraicGeometry.RingedSite.compositionMapOfModels_restrict_square` of Stacks 0A91 together
with the globally strictly perfect case
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_of_isFiniteFreeSummand`. This is
the route that
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.PerfectEvaluation` takes for the
sibling assertion Stacks 0G40.

The source finishes the argument differently, by comparing `Φ` on representatives with the
module-level map `F ⊗_{O_X} Hom_{O_X}(E, O_X) ⟶ Hom_{O_X}(E, F)` as step (5) of its proof
(`Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_localSummand`). The step that plays that
role here is
`AlgebraicGeometry.RingedSite.compositionMap_structureSheafMiddle_quasiIso_of_isFiniteFreeSummand`,
which identifies the composition morphism at intermediate object the structure sheaf with the
interchange morphism of Stacks 0BYT and so inherits the strictly perfect case from it.

## Perfectness model

`AlgebraicGeometry.RingedSite.IsPerfect` of Stacks 08G5 is used, read at the ringed site
`Stacks.SheafOfModules.ringedSite Rc` of opens of the space, exactly as in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.PerfectEvaluation`, whose
"Perfectness model" section records why that notion and not the ringed-space one of Stacks 08CM:
its local condition is phrased with `AlgebraicGeometry.RingedSite.restrictComplex`, restriction
to a slice site, which is the vocabulary of the locality statement used here, while Stacks 08CM
is phrased with restriction to an open *subspace*, for which no comparison is available.

## The registration is unconditional, and the hypothesis is inhabited

Everything the statement needs besides `hK` is supplied by the library, not assumed of the
caller, and both halves of that were machine-checked rather than argued.

*Consumption.* The ambient variable block is eight instances, and all eight are discharged at an
arbitrary `X : TopCat.{u}` and `Rc`: the five sheafification and local-bijectivity ones by
synthesis, and the three tensor ones by `Stacks.SheafOfModules.Tensor.sheafTensor_additive`,
`Tensor.sheafTensor_obj_additive` and `Tensor.hasMapBifunctor_sheafTensor`, which assume
nothing — they have to be pinned by name only because they are stated with the sections universe
tied to the site universes as `max u v`, which synthesis cannot solve against this cluster's
diagonal `u` while those universes are metavariables. That is what
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation` already does, and its
`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_self` is a consumer of the theorem
below at `hK` alone.

*Non-vacuity.* `hK` is inhabited over an arbitrary ringed space, by
`AlgebraicGeometry.RingedSite.isPerfect_of_isZero` of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect` off
`CategoryTheory.Limits.isZero_zero`. That witness is the zero object, so it establishes
satisfiability and not content: the theorem is strictly stronger than the zero case, since the
zero witness proves `IsIso (derivedTensorDualToSheafHom Rc 0 M)` and nothing about a general `K`.
A non-zero witness over an arbitrary ringed space would need `X.IsPerfect` of the structure sheaf
in degree zero, for which the site-level route
`isPerfect_of_forall_coveringFamily_strictlyPerfect` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels` is available only at
`SheafOfModules.{0}`.

*Where the finiteness sits.* Perfectness is required of the **dualized** variable. The
hypothesis cannot be moved to the tensor factor: `K ⊗^L_{O_X} M^∨ ⟶ RSheafHom(M, K)` for a
perfect `K` and arbitrary `M` is a well-typed statement and a false one.

## References

* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Stacks 08DQ, third assertion.** Let `(X, O_X)` be a ringed space, let `K` be a perfect
object of `D(O_X)` and let `M` be any object. The canonical map of Stacks 08I1

`Φ : M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)`

is an isomorphism.

The only hypothesis is perfectness of `K`, in the site-level reading of Stacks 08G5: there is a
complex of `O_X`-modules representing `K` and a covering of the space on each member of which the
restriction of that complex receives a quasi-isomorphism from a strictly perfect complex. The
object `M` is arbitrary.

This is the ringed-site statement
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect` read at the site of
opens of the space, for the canonical derived tensor product. The section "How it is proved" of
this file sets out the argument.

The instances in the ambient variable block are setup, not hypotheses on the lemma: a ringed
space whose slice sites admit sheafification and on which the tensor product of sheaves of
modules is additive and totalisable is what it takes for the objects in the statement — the
derived tensor product, the derived dual, and their restrictions to the slices appearing in the
definition of perfection — to exist at all. -/
@[stacks 08DQ "the third assertion: the canonical map `M ⊗^L K^∨ ⟶ RSheafHom(K, M)` of \
Stacks 08I1 is an isomorphism for a perfect `K`", sga "6 I 7.7" "special case"]
theorem isIso_derivedTensorDualToSheafHom_of_isPerfect
    (K M : DerivedCategory (StructureSheafModules Rc))
    (hK : (ringedSite Rc).IsPerfect K) :
    IsIso (derivedTensorDualToSheafHom Rc K M) :=
  RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) K M hK

end Stacks.SheafOfModules

end
