module

public import StacksFrontier.CategoryTheory.Monoidal.ReseatExactPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackMonoidalFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived pullback commutes with the derived dual of a perfect object

Let `f : (X, O_X) ⟶ (Y, O_Y)` be a morphism of ringed spaces and let `E` in `D(O_Y)` be perfect
with perfect derived pullback. Then

`Lf^*(E^∨) ≅ (Lf^*E)^∨`.

By `Stacks.SheafOfModules.exactPairingDerivedDual` ([Stacks, Tag 0FPC]) `E^∨` is a left dual of
`E`, and by `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal` ([Stacks, Tag 079U])
`Lf^*` is a monoidal functor. `CategoryTheory.ExactPairing.map` carries a left dual along a
monoidal functor, so `Lf^*(E^∨)` is a left dual of `Lf^*E`; `(Lf^*E)^∨` is another, so the two
agree by uniqueness of duals, `CategoryTheory.rightDualIso`.

## Main results

* `Stacks.SheafOfModules.exactPairingDerivedDualCanonical`: [Stacks, Tag 0FPC] restated at
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`.
* `Stacks.SheafOfModules.exactPairingDerivedPullbackDual`: `Lf^*(E^∨)` is a left dual of `Lf^*E`.
* `Stacks.SheafOfModules.derivedPullbackDerivedDualIso`: **`Lf^*(E^∨) ≅ (Lf^*E)^∨`.**

## Implementation notes

[Stacks, Tag 0FPC] is proved at `Stacks.SheafOfModules.derivedMonoidalStructure` and the
coherence of [Stacks, Tag 079U] at
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. These are two re-seatings of
the same monoidal derived category of [Stacks, Tag 0FPT] along the same unit isomorphism
`Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso`, differing only in the tensor bifunctor
they are seated on, so `CategoryTheory.MonoidalCategory.exactPairingReseatOfReseat` moves the
pairing from one to the other.

Both perfectness hypotheses are used: `E` perfect gives `E^∨` its pairing on `Y`, and `Lf^*E`
perfect gives `(Lf^*E)^∨` its pairing on `X`.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

section Canonical

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (K : DerivedCategory (StructureSheafModules Rc))

/-- **The derived dual of a perfect object is a left dual for the monoidal structure of
Tag 0FPT re-seated on the derived tensor product of Tag 06YU**, that is, for
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`. -/
@[instance_reducible, sga "6 I 7.8" "special case"]
def exactPairingDerivedDualCanonical (hK : (ringedSite Rc).IsPerfect K) :
    @ExactPairing _ _ (DerivedMonoidal.canonicalDerivedMonoidal Rc) K (derivedDual Rc K) :=
  @exactPairingReseatOfReseat _ _ (DerivedMonoidal.derivedMonoidal Rc) _ _ _
    (derivedTensorMonoidalIso Rc) (DerivedMonoidal.monoidalTensorCanonicalIso Rc)
    (DerivedMonoidal.canonicalUnitIso Rc) K (derivedDual Rc K)
    (exactPairingDerivedDual Rc K hK)

end Canonical

section Pullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

/-- **The derived pullback of the derived dual is a left dual of the derived pullback.**
This is the image of the pairing `exactPairingDerivedDualCanonical` on `Y` under the monoidal
functor `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal`. -/
@[instance_reducible]
def exactPairingDerivedPullbackDual (E : DerivedCategory (StructureSheafModules Y.sheaf))
    (hE : (ringedSite Y.sheaf).IsPerfect E) :
    @ExactPairing _ _ (DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
      ((derivedPullback f).obj E) ((derivedPullback f).obj (derivedDual Y.sheaf E)) :=
  @ExactPairing.map _ _ _ _ (DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf)
    (DerivedMonoidal.canonicalDerivedMonoidal X.sheaf) (derivedPullback f)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal f) E (derivedDual Y.sheaf E)
    (exactPairingDerivedDualCanonical Y.sheaf E hE)

/-- **`Lf^*(E^∨) ≅ (Lf^*E)^∨`** for a perfect `E` in `D(O_Y)` whose derived pullback is perfect.

It is the canonical isomorphism `CategoryTheory.rightDualIso` between the two left duals
`exactPairingDerivedPullbackDual` and `exactPairingDerivedDualCanonical` (on `X`) of `Lf^*E`. -/
def derivedPullbackDerivedDualIso (E : DerivedCategory (StructureSheafModules Y.sheaf))
    (hE : (ringedSite Y.sheaf).IsPerfect E)
    (hfE : (ringedSite X.sheaf).IsPerfect ((derivedPullback f).obj E)) :
    (derivedPullback f).obj (derivedDual Y.sheaf E) ≅
      derivedDual X.sheaf ((derivedPullback f).obj E) :=
  @rightDualIso _ _ (DerivedMonoidal.canonicalDerivedMonoidal X.sheaf) _ _ _
    (exactPairingDerivedPullbackDual f E hE)
    (exactPairingDerivedDualCanonical X.sheaf ((derivedPullback f).obj E) hfE)

end Pullback

end Stacks.SheafOfModules

end
