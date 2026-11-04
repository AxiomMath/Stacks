module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftTwo
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
import StacksCore.Tactic.StacksAttribute

/-!
# The first leg of the shift compatibility of the comparison of Tag 079U

`Stacks.Cohomology.DerivedPullbackTensor.ModelsComparisonCommShift₂` is built from three
transformations, and the compatibility with the shift of each is a separate obligation.  This
file discharges the first: the comparison
`Lf^*(QM) ⟶ Q(f^*M)` of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` commutes with the shift.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTransAssoc`: the same
  transformation with the three reassociations of its five intermediate functors written out as
  `CategoryTheory.Functor.associator`s.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTransAssoc_eq`: it *is* the same
  transformation — the associators are the identity on every object.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans_commShift`: **the first leg.**

## Implementation notes

**Why the associators have to be written out, and why without them the search cannot succeed
at any heartbeat budget.**  `derivedPullbackNatTrans f` is a composite of four whiskerings, and
each of its three junctions joins two *differently bracketed* spellings of one functor: the first
factor lands in `(quotient ⋙ Qh) ⋙ Lf^*` while the second starts from
`quotient ⋙ (Qh ⋙ Lf^*)`.  `CategoryTheory.Functor.comp` is definitionally associative, so the
composite type-checks; but `CategoryTheory.NatTrans.CommShift.comp` consumes the *middle functor's
`CategoryTheory.Functor.CommShift` datum*, and `Functor.CommShift.comp (F ⋙ G) H` is **not**
definitionally `Functor.CommShift.comp F (G ⋙ H)` — the two commutation isomorphisms are
assembled in different orders and differ by an associator, which is the identity on objects but
not by `rfl`.  Instance search therefore proposes `comp` at each junction and spends its whole
budget on a `isDefEq` that cannot succeed: the composite exhausts
`synthInstance`'s 20000 heartbeats, and a run with the five intermediate data seated by hand
exhausts `isDefEq`'s 200000 as well.  Raising either limit would not help, because the equation is
not a definitional one.

Inserting the three associators makes every junction match on the nose, and
`CategoryTheory.NatTrans.CommShift.associator` supplies each one's own compatibility.  What is
then left for the caller is only *per-factor seating*: the four whiskered factors each need their
inputs present as **local** instances, since the pullback development's `𝒪_Y` and the tensor
development's are the same sheaf only up to the reducibility attributes repeated below, and a
local instance is tried by class name rather than through the discrimination tree.

**`Lf^*`'s own commutation is seated in the *type*.**  `NatTrans.CommShift` takes the source and
target functors' `Functor.CommShift` data as *instance arguments*, so they are synthesized while
the statement is elaborated — before any `haveI` in a proof is in scope.  Hence the `letI` in the
statement of `derivedPullbackNatTrans_commShift`; a consumer has to repeat it, exactly as it has
to repeat the reducibility attributes.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback
  derivedPullbackComparison pullbackOnHomotopy)
open Stacks.Cohomology.KFlatDerivedPullback (derivedPullback_commShift
  derivedPullbackComparison_commShift)

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- `derivedPullbackNatTrans f` with its three reassociations written out.  Every junction of
this composite joins two syntactically equal functors, which is what lets
`CategoryTheory.NatTrans.CommShift.comp` apply at each of them. -/
def derivedPullbackNatTransAssoc :
    DerivedCategory.Q ⋙ derivedPullback f ⟶ pullbackComplex f ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Modules Y)).inv
      (derivedPullback f) ≫
    (Functor.associator (HomotopyCategory.quotient (Modules Y) (ComplexShape.up ℤ))
      DerivedCategory.Qh (derivedPullback f)).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (Modules Y) (ComplexShape.up ℤ))
      (derivedPullbackComparison f) ≫
    (Functor.associator (HomotopyCategory.quotient (Modules Y) (ComplexShape.up ℤ))
      ((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).inv ≫
    Functor.whiskerRight ((RingedSpaceModuleAdjunction.modulePullback f
      ).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    (Functor.associator
      ((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient (Modules X) (ComplexShape.up ℤ)) DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft
      ((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (Modules X)).hom

/-- The reassociated composite is `derivedPullbackNatTrans f`: a
`CategoryTheory.Functor.associator` is the identity on every object. -/
theorem derivedPullbackNatTransAssoc_eq :
    derivedPullbackNatTransAssoc f = derivedPullbackNatTrans f := by
  unfold derivedPullbackNatTransAssoc derivedPullbackNatTrans
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  show _ ≫ _ ≫ _ ≫ 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- **The first leg of the shift compatibility of the comparison of [Stacks, Tag 079U]**: the
comparison `Lf^*(QM) ⟶ Q(f^*M)` of a complex commutes with the shift.

Everything is in place once the four whiskered factors are seated one at a time and the three
reassociations of the intermediate functors are written out; see the implementation notes. -/
theorem derivedPullbackNatTrans_commShift :
    letI := derivedPullback_commShift f
    NatTrans.CommShift (derivedPullbackNatTrans f) ℤ := by
  letI := derivedPullback_commShift f
  -- the inputs the four whiskered factors' own instances consume
  letI : (HomotopyCategory.quotient (Modules Y) (ComplexShape.up ℤ)).CommShift ℤ := inferInstance
  letI : (DerivedCategory.Qh ⋙ derivedPullback f).CommShift ℤ := inferInstance
  letI : (pullbackOnHomotopy f).CommShift ℤ := inferInstance
  letI := derivedPullbackComparison_commShift f
  letI : NatTrans.CommShift (derivedPullbackNatTransAssoc f) ℤ := by
    unfold derivedPullbackNatTransAssoc
    infer_instance
  exact NatTrans.commShift_of_eq (derivedPullbackNatTransAssoc_eq f).symm

end Stacks.Cohomology.DerivedPullbackTensor

end
