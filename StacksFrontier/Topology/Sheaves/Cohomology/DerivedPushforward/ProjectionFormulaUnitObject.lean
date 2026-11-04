module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitCoherenceMonoidal

/-!
# The base case of the derived projection formula, unconditionally

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `E ∈ D(𝒪_X)`.
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap` ([Stacks, Tag 0B53]) is the
canonical morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`,

and [Stacks, Tag 08EU] asserts that it is an isomorphism.  **This file proves the case
`K = 𝒪_Y[0]` — the case the source's proof calls immediate, and the base of its dévissage in the
target complex — with nothing carried**, for an arbitrary morphism of ringed spaces and an
arbitrary `E`.

Everything is already in place, and this module declares nothing of its own but the result.
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_of_monoidal`
proves the base case from one hypothesis, that `f^*` carries a monoidal structure for the tensor
product sheaf of [Stacks, Tag 01CA] whose oplax tensorator is the comparison of
[Stacks, Tag 01CD].  Both halves of that hypothesis already exist, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence`: the
structure is `Stacks.Cohomology.DerivedPullbackTensor.liftMonoidal`, which is
`Stacks.PullbackSheafTensor.monoidal` ascribed at the spelling of the functor and of the ring
sheaf used here, and the prescription of its tensorator is
`Stacks.Cohomology.DerivedPullbackTensor.isComparisonTensorator_sheafTensor`.  This module
imports that one and applies them; neither is restated.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_unconditional`:
  **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]`, carrying nothing.**

## What is proved and what is not

The statement is more general than the source's in every respect but one: no quasi-compactness,
no quasi-separatedness, no quasi-coherence and no hypothesis on `E`, for an arbitrary morphism of
ringed spaces.  The one respect is `K`: it is the structure sheaf in degree **zero**, not a
general object of `D_QCoh(𝒪_Y)`.

The dévissage from here to a general `K` is
`Stacks.Cohomology.DerivedProjectionFormulaDevissage.isIso_projectionFormulaMap_of_generation`,
whose two steps — arbitrary direct sums and distinguished triangles — are unconditional.  It
consumes three inputs that this file does not supply, and all three remain open:

* the base case at `𝒪_Y[i]` for **every** `i`, not only `i = 0`.  The projection-formula morphism
  is not known to commute with the shift — that compatibility of [Stacks, Tag 079U] is not among
  the ones `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` comes with — so the
  case `i = 0` proved here does not give the others;
* the preservation of arbitrary direct sums by the two sides, of which the substantial part is
  [Stacks, Tag 08DZ] for `Rf_*`;
* the generation of `D(𝒪_Y)` by its structure sheaf in the sense of [Stacks, Tag 09PB].

## Implementation notes

**Why this is a separate module.**  The monoidal structure of `f^*` cannot be seated in the
module that consumes it:
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal` drags in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso`, after which instance search no
longer synthesizes `HasFiniteCoproducts (Mod 𝒪_Z)` — nor `HasZeroObject (Mod 𝒪_Z)`, which the
total tensor product of complexes needs.  `PullbackTensorComplexCoherence` lives with that
import and works around it by naming `Abelian (Mod 𝒪_Z)` by hand; nothing below mentions complexes
at all, so the import costs nothing here.  The coherence itself is proved one module down,
where the import is absent and the structure is a binder.

**The two retypings.**  `Stacks.PullbackSheafTensor.monoidal` is stated for
`Stacks.RingedSpace.pullbackFunctor`, over `Stacks.RingedSpace.structureRingSheaf`, while the
degreewise pullback of a complex is `StacksDraft.KFlat.modulePullback`, over
`Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf`.  Both pairs are the same term, and the
crossing is already performed once, by `Stacks.Cohomology.DerivedPullbackTensor.liftMonoidal`,
which is why that declaration is seated here rather than a second ascription written out: a
second one would be the same statement and the same body under a second name.  No reducibility
opt-in is needed in this module, and in particular no ring-sheaf spelling is made reducible
anywhere.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard monoidalModules
attribute [local instance] Stacks.Cohomology.DerivedPullbackTensor.liftMonoidal

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

end Stacks.Cohomology.DerivedProjectionFormula

end
