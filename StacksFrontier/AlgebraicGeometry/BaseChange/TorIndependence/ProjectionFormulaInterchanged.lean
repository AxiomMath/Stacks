module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethSchemeTorIndependent
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ProjectionFormulaDischarged
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductCommutativity
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 08EU] with the two tensor factors interchanged

[Stacks, Tag 08EU] says that for a quasi-compact quasi-separated morphism of schemes `f : X ⟶ S`
and complexes `K` on `X` and `A` on `S` with quasi-coherent cohomology the projection-formula
morphism

`Rf_*K ⊗^𝐋_{𝒪_S} A ⟶ Rf_*(K ⊗^𝐋_{𝒪_X} Lf^*A)`

is invertible; it is proved as `AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent`.  This
module gives the same statement with the two tensor factors in the other order,

`A ⊗^𝐋_{𝒪_S} Rf_*K ⟶ Rf_*(Lf^*A ⊗^𝐋_{𝒪_X} K)`,

which is the order [Stacks, Tag 08I9] produces and therefore the order the reduction of
[Stacks, Tag 08IB] to [Stacks, Tag 08EU] consumes.

Nothing new is proved: the two orders are conjugate by the commutativity constraints of
[Stacks, Tag 0FPB] on `D(𝒪_S)` and on `D(𝒪_X)`, which are invertible, and the conjugation needs
only their naturality and their compatibility with the derived pullback–tensor comparison of
[Stacks, Tag 079U].  The three inputs are
`Stacks.Cohomology.DerivedKunneth.isIso_derivedBraiding`,
`Stacks.Cohomology.DerivedRelativeCupProduct.derivedBraiding_naturality` and
`Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonBraided`.

## Main results

* `AlgebraicGeometry.isIso_adjunctionTensorMapRight_of_quasicoherent`: **[Stacks, Tag 08EU] in
  the interchanged order.**

## Implementation notes

The pullback–pushforward development spells the structure sheaf of a ringed space
`structureSheafRing` and the tensor-product development spells it
`Stacks.SheafOfModules.Tensor.ringSheaf`; the two are equal by `rfl` and not syntactically, and
the commutativity constraint is stated at the second spelling while the projection formula is
stated at the first.  As in
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/KunnethSchemeTorIndependent.lean`, the
crossing is made by declaring `structureSheafRing` locally `implicit_reducible`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedAdjunction derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedProjectionFormula (pullbackTensorComparison)
open Stacks.Cohomology.DerivedRelativeCupProduct (derivedBraiding derivedBraiding_naturality
  pullbackTensorComparisonBraided)
open Stacks.Cohomology.DerivedKunneth (adjunctionTensorMapRight isIso_derivedBraiding
  isIso_adjunctionTensorMapRight_of_braiding)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing

/-- **[Stacks, Tag 08EU] with the two tensor factors interchanged.**  For a quasi-compact
quasi-separated morphism of schemes `f : X ⟶ S` and complexes `K` on `X` and `A` on `S` with
quasi-coherent cohomology, the interchanged-order projection-formula morphism

`A ⊗^𝐋_{𝒪_S} Rf_*K ⟶ Rf_*(Lf^*A ⊗^𝐋_{𝒪_X} K)`

is invertible.

This is `AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent` conjugated by the
commutativity constraints of [Stacks, Tag 0FPB], through
`Stacks.Cohomology.DerivedKunneth.isIso_adjunctionTensorMapRight_of_braiding`. -/
theorem isIso_adjunctionTensorMapRight_of_quasicoherent {X S : Scheme.{u}} (f : X ⟶ S)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent)
    (hA : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj A).IsQuasicoherent) :
    IsIso (adjunctionTensorMapRight (derivedAdjunction f.toLRSHom.toShHom)
      (Functor.uncurry.obj (derivedTensorProductFunctor S.toRingedSpace.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
      (pullbackTensorComparison f.toLRSHom.toShHom) A K) :=
  isIso_adjunctionTensorMapRight_of_braiding (derivedAdjunction f.toLRSHom.toShHom)
    (Functor.uncurry.obj (derivedTensorProductFunctor S.toRingedSpace.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
    (pullbackTensorComparison f.toLRSHom.toShHom)
    (derivedBraiding S.toRingedSpace) (derivedBraiding X.toRingedSpace)
    (fun g g' => derivedBraiding_naturality X.toRingedSpace g g')
    (pullbackTensorComparisonBraided f.toLRSHom.toShHom) A K
    (isIso_derivedBraiding S.toRingedSpace _ _) (isIso_derivedBraiding X.toRingedSpace _ _)
    (projectionFormulaIsIsoOnQuasicoherent f hqc hqs K A hK hA)

end AlgebraicGeometry

end
