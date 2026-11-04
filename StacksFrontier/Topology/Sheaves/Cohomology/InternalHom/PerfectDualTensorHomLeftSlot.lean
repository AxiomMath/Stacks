module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHomFunctorial
import StacksCore.Tactic.StacksAttribute

/-!
# The third assertion of Stacks 08DQ with the dual in the left tensor slot

Let `(X, O_X)` be a ringed space and let `K` be a perfect object of `D(O_X)`. The third
assertion of **Stacks 08DQ** identifies the derived internal hom out of `K` with a tensor
product against the dual `K^∨`, functorially. `Stacks.SheafOfModules.derivedTensorDualNatIso`
states it with the dual in the **right** tensor slot,

`(- ⊗^L_{O_X} K^∨) ≅ RSheafHom(K, -)`,

as the canonical map of [Stacks, Tag 08I1] is written. This file gives the **left**-slot form

`(K^∨ ⊗^L_{O_X} -) ≅ RSheafHom(K, -)`,

which is the shape the consumers of the tag ask for.

## Main results

* `Stacks.SheafOfModules.derivedTensorBraidingNatIso`: the commutativity constraint of
  `D(O_X)` read as a natural isomorphism `(A ⊗^L_{O_X} -) ≅ (- ⊗^L_{O_X} A)` of functors on
  `D(O_X)`.
* `Stacks.SheafOfModules.derivedTensorDualNatIsoLeft`: **Stacks 08DQ, third assertion**, in the
  left tensor slot, for a perfect `K`.
* `Stacks.SheafOfModules.derivedTensorDualNatIsoLeftOfIsPerfectSpace`: the same at the
  ringed-space perfectness hypothesis of [Stacks, Tag 08CM].

## Implementation notes

The passage between the two slots is the commutativity constraint of [Stacks, Tag 0FPT]. The
implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHomFunctorial` recorded
that this constraint was **not available** for `Stacks.SheafOfModules.derivedTensor` — that the
library's braiding belonged to an unrelated structure also called `DerivedTensorProduct`, so
that giving the left-slot form needed either a commutativity constraint for this cluster's
tensor product or a comparison of the two, and that neither was in the library. That is not so.
`Stacks.SheafOfModules.derivedMonoidalStructure` is a monoidal structure on `D(O_X)` whose
curried tensor product is `Stacks.SheafOfModules.derivedTensor` **on the nose** —
`Stacks.SheafOfModules.curriedTensor_derivedMonoidalStructure` is `rfl` — and
`Stacks.SheafOfModules.derivedSymmetricStructure` is its commutativity constraint, the Koszul
symmetry of [Stacks, Tag 0FNI] transported from complexes. Both are universe polymorphic. So
the braiding applies to this cluster's tensor product directly, and the naturality square that
`NatIso.ofComponents` asks of it is literally
`CategoryTheory.BraidedCategory.braiding_naturality_right`.

Both structures are brought in as local instances rather than global ones, as every file of
this cluster that needs a monoidal structure on `D(O_X)` does.

The left-slot isomorphism is **not** claimed to be carried by the canonical map of
[Stacks, Tag 08I1]: that map is written with the dual on the right, and what is asserted here
is the composite of it with the braiding. The right-slot form
`Stacks.SheafOfModules.derivedTensorDualNatIso` is the one that is the canonical map.

## References

* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FNI](https://stacks.math.columbia.edu/tag/0FNI)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Definition 20.46.4 (Tag 08CM)](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry
open StrictlyPerfect

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

section Site

variable {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y)
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The commutativity constraint of `D(O_X)` as a natural isomorphism of functors.** For an
object `A` of `D(O_X)` the braidings `A ⊗^L_{O_X} M ≅ M ⊗^L_{O_X} A` assemble into an
isomorphism of functors `(A ⊗^L_{O_X} -) ≅ (- ⊗^L_{O_X} A)` on `D(O_X)`.

The two functors are the two one-variable restrictions of `Stacks.SheafOfModules.derivedTensor`,
whose bifunctor is the curried tensor product of
`Stacks.SheafOfModules.derivedMonoidalStructure` on the nose, so the components are the
braidings of that structure and the naturality square is
`CategoryTheory.BraidedCategory.braiding_naturality_right`. -/
def derivedTensorBraidingNatIso (A : DerivedCategory (StructureSheafModules Rc)) :
    (derivedTensor Rc).obj A ≅ (derivedTensor Rc).flip.obj A :=
  NatIso.ofComponents (fun M => β_ A M)
    (fun f => BraidedCategory.braiding_naturality_right A f)

variable
  [∀ V : Opens Y, HasSheafify ((Opens.grothendieckTopology Y).over V) AddCommGrpCat.{u}]
  [∀ V : Opens Y, ((Opens.grothendieckTopology Y).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens Y, HasWeakSheafify ((Opens.grothendieckTopology Y).over V) AddCommGrpCat.{u}]
  (K : DerivedCategory (StructureSheafModules Rc))

/-- **Stacks 08DQ, third assertion, with the dual in the left tensor slot.** For a perfect
object `K` of `D(O_X)` there is an isomorphism of functors

`(K^∨ ⊗^L_{O_X} -) ≅ RSheafHom(K, -)`

on `D(O_X)`, which is the source's assertion that the identification is functorial in the
second variable, written with the dual tensored on the left.

It is `Stacks.SheafOfModules.derivedTensorDualNatIso`, the same assertion with the dual in the
right slot, precomposed with the commutativity constraint of
`Stacks.SheafOfModules.derivedTensorBraidingNatIso`. Unlike the right-slot form, it is not
claimed to be carried by the canonical map of [Stacks, Tag 08I1]; see the implementation
notes. -/
@[stacks 08DQ "the third assertion as a natural isomorphism of functors on D(O_X), with the \
dual in the LEFT tensor slot rather than the right one in which Tag 08I1 writes the canonical \
map and in which `Stacks.SheafOfModules.derivedTensorDualNatIso` states it; the two differ by \
the commutativity constraint of Tag 0FPT, so this one is NOT claimed to be carried by the \
canonical map"]
def derivedTensorDualNatIsoLeft (hK : (ringedSite Rc).IsPerfect K) :
    (derivedTensor Rc).obj (derivedDual Rc K) ≅ (derivedSheafHom Rc).obj (op K) :=
  derivedTensorBraidingNatIso Rc (derivedDual Rc K) ≪≫ derivedTensorDualNatIso Rc K hK

end Site

section Space

variable (X : RingedSpace.{u, u}) (K : DerivedCategory (OXMod.{u, u} X))

/-- **Stacks 08DQ, third assertion in the left tensor slot, at the ringed-space hypothesis.**
As `Stacks.SheafOfModules.derivedTensorDualNatIsoLeft`, with perfectness of `K` read as
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, the notion of [Stacks, Tag 08CM]. -/
@[stacks 08DQ "the third assertion as a natural isomorphism with the dual in the LEFT tensor \
slot, with perfectness in the RINGED-SPACE reading of Tag 08CM rather than the site reading of \
Tag 08G5 that `Stacks.SheafOfModules.derivedTensorDualNatIsoLeft` uses"]
def derivedTensorDualNatIsoLeftOfIsPerfectSpace
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    (derivedTensor X.sheaf).obj (derivedDual X.sheaf K) ≅
      (derivedSheafHom X.sheaf).obj (op K) :=
  derivedTensorDualNatIsoLeft X.sheaf K
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK)

end Space

end Stacks.SheafOfModules

end
