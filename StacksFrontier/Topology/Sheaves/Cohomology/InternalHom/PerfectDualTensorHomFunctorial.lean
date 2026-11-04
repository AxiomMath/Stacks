module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom
import StacksCore.Tactic.StacksAttribute

/-!
# The third assertion of Stacks 08DQ as a natural isomorphism of functors

Let `(X, O_X)` be a ringed space and let `K` be a perfect object of `D(O_X)`. The third
assertion of **Stacks 08DQ** is that the canonical map of [Stacks, Tag 08I1]

`M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)`

is an isomorphism, *functorially in `M`*.
`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect` is the invertibility at a
fixed `M` and `Stacks.SheafOfModules.derivedTensorDualToSheafHom_naturality` is the
functoriality; this file assembles the two into the single natural isomorphism of functors on
`D(O_X)` that the source's word "functorial" asserts, and gives it in both tensor slots.

## Main results

* `Stacks.SheafOfModules.derivedTensorDualNatIso`: `(- ⊗^L_{O_X} K^∨) ≅ RSheafHom(K, -)` as
  functors `D(O_X) ⥤ D(O_X)`, for a perfect `K`.
* `Stacks.SheafOfModules.derivedTensorDualNatIsoOfIsPerfectSpace`: the same at the ringed-space
  perfectness hypothesis of [Stacks, Tag 08CM], as in
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis`.

## Implementation notes

The naturality square `NatIso.ofComponents` asks for is literally the statement of
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_naturality`, the canonical map being natural
in the tensor variable; no rewriting is needed.

The dual sits in the **right** tensor slot, as the canonical map of [Stacks, Tag 08I1] is
written and as the source writes the assertion. A consumer that wants to tensor *with* the dual
needs the left slot — for instance the `iso` field of
`Stacks.Cohomology.ExtProjectionFormulaQuasiCoherent.DualSheafHomData`, which asks for
`E^∨ ⊗^L_{O_X} - ≅ RSheafHom(E, -)`. The passage between the slots is the commutativity
constraint of [Stacks, Tag 0FPT], which is unconditional, and **at this cluster's spelling it
is available**: `Stacks.SheafOfModules.derivedSymmetricStructure` is a commutativity constraint
for `Stacks.SheafOfModules.derivedMonoidalStructure`, whose curried tensor product is
`Stacks.SheafOfModules.derivedTensor` on the nose
(`Stacks.SheafOfModules.curriedTensor_derivedMonoidalStructure` is `rfl`). The left-slot form
is therefore
`Stacks.SheafOfModules.derivedTensorDualNatIsoLeft`, in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHomLeftSlot`. The
braiding `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` belongs to the
unrelated second structure of that name and is not this constraint.

The `DualSheafHomData` consumer is not discharged by it: that
field is stated at `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the second
structure's tensor product, and a comparison of the two tensor products is what it would
need.

## References

* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Definition 20.46.4 (Tag 08CM)](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open StrictlyPerfect

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

section Site

variable {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y)
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens Y, HasSheafify ((Opens.grothendieckTopology Y).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y, ((Opens.grothendieckTopology Y).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens Y, HasWeakSheafify ((Opens.grothendieckTopology Y).over V) AddCommGrpCat.{u}]
  (K : DerivedCategory (StructureSheafModules Rc))

/-- **Stacks 08DQ, third assertion, as a natural isomorphism.** For a perfect object `K` of
`D(O_X)` the canonical maps `M ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, M)` of [Stacks, Tag 08I1] assemble
into an isomorphism of functors

`(- ⊗^L_{O_X} K^∨) ≅ RSheafHom(K, -)`,

which is the source's assertion that the identification is functorial in `M`. Its component at
`M` is the canonical map, invertible by
`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`; the naturality square is
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_naturality`. -/
@[stacks 08DQ "the third assertion as a natural isomorphism of functors on D(O_X), i.e. together \
with the FUNCTORIALITY in M that the source asserts; its component at M is the canonical map of \
Tag 08I1 and is the content of \
`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`"]
def derivedTensorDualNatIso (hK : (ringedSite Rc).IsPerfect K) :
    (derivedTensor Rc).flip.obj (derivedDual Rc K) ≅ (derivedSheafHom Rc).obj (op K) :=
  NatIso.ofComponents
    (fun M =>
      haveI := isIso_derivedTensorDualToSheafHom_of_isPerfect Rc K M hK
      asIso (derivedTensorDualToSheafHom Rc K M))
    fun {_ _} m => derivedTensorDualToSheafHom_naturality Rc K m

end Site

section Space

variable (X : RingedSpace.{u, u}) (K : DerivedCategory (OXMod.{u, u} X))

/-- **Stacks 08DQ, third assertion, as a natural isomorphism, at the ringed-space hypothesis.**
As `Stacks.SheafOfModules.derivedTensorDualNatIso`, with perfectness of `K` read as
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, the notion of [Stacks, Tag 08CM]. -/
@[stacks 08DQ "the third assertion as a natural isomorphism of functors, with perfectness in the \
RINGED-SPACE reading of Tag 08CM rather than the site reading of Tag 08G5 that \
`Stacks.SheafOfModules.derivedTensorDualNatIso` uses"]
def derivedTensorDualNatIsoOfIsPerfectSpace
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    (derivedTensor X.sheaf).flip.obj (derivedDual X.sheaf K) ≅
      (derivedSheafHom X.sheaf).obj (op K) :=
  derivedTensorDualNatIso X.sheaf K
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK)

end Space

end Stacks.SheafOfModules

end
