module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksCore.Tactic.StacksAttribute

/-!
# The subcategories of cohomological descent of a morphism of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `Lf^* ⊣ Rf_*` the
derived adjunction between `D(O_D)` and `D(O_C)`. Consider

* the full subcategory `D' ⊆ D(O_D)` of the objects `K` with `K ⟶ Rf_* Lf^* K` invertible, and
* the full subcategory `D' ⊆ D(O_C)` of the objects `K` with `Lf^* Rf_* K ⟶ K` invertible.

Each is a saturated triangulated strictly full subcategory, `Lf^*` is fully faithful on the
first and `Rf_*` is fully faithful on the second.

## Main results

* `Stacks.Cohomology.CohomologicalDescent.unitIsIso_saturated_triangulated_fullyFaithful`:
  the statement for the unit.
* `Stacks.Cohomology.CohomologicalDescent.counitIsIso_saturated_triangulated_fullyFaithful`:
  the statement for the counit.
* `Stacks.Cohomology.CohomologicalDescent.derivedAdjunction_isTriangulated`: the derived
  adjunction is an adjunction of triangulated functors, `Rf_*` carrying the commutation with the
  shift induced by the one of `Lf^*`.

## Implementation notes

The derived adjunction is `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`, which
exists for every morphism of ringed topoi, and the exactness of `Lf^*` is
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_isTriangulated`. The exactness of
`Rf_*` then follows formally: the commutation of `Rf_*` with the shift is transported from that of
`Lf^*` along the adjunction (`CategoryTheory.Adjunction.rightAdjointCommShift`), the adjunction
is compatible with the two by construction, and a right adjoint of a triangulated functor is
triangulated (`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`). Being a triangulated
subcategory is a property of a subcategory of a triangulated category, so the choice of these
commutation isomorphisms does not enter the statements.

With this in place the two statements are the corresponding facts about an arbitrary exact
adjunction, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms`.

## References

* [Stacks Project, Tag 0D7Q](https://stacks.math.columbia.edu/tag/0D7Q)
* [Stacks Project, Tag 0D7R](https://stacks.math.columbia.edu/tag/0D7R)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward Stacks.Cohomology.DerivedPullbackOfToposHom

noncomputable section

universe u

namespace Stacks.Cohomology.CohomologicalDescent

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

private instance : (derivedPushforward (X := X) (Y := Y) f).CommShift ℤ :=
  (derivedAdjunction f).rightAdjointCommShift ℤ

private instance : (derivedAdjunction f).CommShift ℤ :=
  (derivedAdjunction f).commShift_of_leftAdjoint ℤ

/-- **The derived adjunction `Lf^* ⊣ Rf_*` of a morphism of ringed topoi is an adjunction of
exact functors**, for the commutation of `Lf^*` with the shift and the one of `Rf_*` induced by
it: `Lf^*` is exact by Tag 06YY, the adjunction is compatible with the shifts by construction,
and a right adjoint of an exact functor is exact. -/
lemma derivedAdjunction_isTriangulated :
    letI := (derivedAdjunction f).rightAdjointCommShift ℤ
    letI : (derivedAdjunction f).CommShift ℤ := (derivedAdjunction f).commShift_of_leftAdjoint ℤ
    (derivedAdjunction f).IsTriangulated := by
  have := derivedPullback_isTriangulated f
  exact Adjunction.IsTriangulated.mk' _

private instance : (derivedAdjunction f).IsTriangulated := derivedAdjunction_isTriangulated f

/-- **The subcategory of `D(O_D)` on which the unit of `Lf^* ⊣ Rf_*` is invertible.** For a
morphism of ringed topoi `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, the full subcategory `D'` of
`D(O_D)` of the objects `K` such that the unit `K ⟶ Rf_* Lf^* K` is an isomorphism is strictly
full (closed under isomorphisms), saturated and triangulated, and `Lf^* : D' ⥤ D(O_C)` is full
and faithful. -/
@[stacks 0D7Q]
theorem unitIsIso_saturated_triangulated_fullyFaithful :
    (derivedAdjunction f).unitIsIso.IsClosedUnderIsomorphisms ∧
      (derivedAdjunction f).unitIsIso.IsSaturated ∧
      (derivedAdjunction f).unitIsIso.IsTriangulated ∧
      ((derivedAdjunction f).unitIsIso.ι ⋙ derivedPullback f).Full ∧
      ((derivedAdjunction f).unitIsIso.ι ⋙ derivedPullback f).Faithful := by
  exact ⟨(derivedAdjunction f).isClosedUnderIsomorphisms_unitIsIso, inferInstance,
    inferInstance, (derivedAdjunction f).fullyFaithfulιCompLeftAdjoint.full,
    (derivedAdjunction f).fullyFaithfulιCompLeftAdjoint.faithful⟩

/-- **The subcategory of `D(O_C)` on which the counit of `Lf^* ⊣ Rf_*` is invertible.** For a
morphism of ringed topoi `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, the full subcategory `D'` of
`D(O_C)` of the objects `K` such that the counit `Lf^* Rf_* K ⟶ K` is an isomorphism is strictly
full (closed under isomorphisms), saturated and triangulated, and `Rf_* : D' ⥤ D(O_D)` is full
and faithful. -/
@[stacks 0D7R]
theorem counitIsIso_saturated_triangulated_fullyFaithful :
    (derivedAdjunction f).counitIsIso.IsClosedUnderIsomorphisms ∧
      (derivedAdjunction f).counitIsIso.IsSaturated ∧
      (derivedAdjunction f).counitIsIso.IsTriangulated ∧
      ((derivedAdjunction f).counitIsIso.ι ⋙ derivedPushforward (X := X) (Y := Y) f).Full ∧
      ((derivedAdjunction f).counitIsIso.ι ⋙ derivedPushforward (X := X) (Y := Y) f).Faithful := by
  exact ⟨(derivedAdjunction f).isClosedUnderIsomorphisms_counitIsIso, inferInstance,
    inferInstance, (derivedAdjunction f).fullyFaithfulιCompRightAdjoint.full,
    (derivedAdjunction f).fullyFaithfulιCompRightAdjoint.faithful⟩

end Stacks.Cohomology.CohomologicalDescent

end

end
