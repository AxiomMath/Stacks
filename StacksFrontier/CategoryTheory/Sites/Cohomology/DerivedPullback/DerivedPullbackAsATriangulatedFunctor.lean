module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 06YY with the existence of `Lf^*` seated rather than assumed

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi.  Tag 06YY asserts that there
is an exact functor of triangulated categories

`Lf^* : D(O') ⟶ D(O)`

with `Lf^* K^• = f^* K^•` for every K-flat complex `K^•` of `O'`-modules with flat terms, hence in
particular for every bounded above complex of flat `O'`-modules.

`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy` proves
that `Lf^*` exists along every morphism of ringed topoi.  The clauses of Tag 06YY that mention
`Lf^*` by name are nevertheless stated there under an **instance binder** for that existence,
because the functor cannot be written down without it.  This file restates them with the witness
supplied inside the statement, so that each conclusion carries exactly the hypotheses of the
source: `f`, and the morphism-of-sites condition on `f.u`.

## Main results

* `derivedPullbackCommShift`: **`Lf^*` commutes with the shift.**  Together with the next result
  this is the assertion that `Lf^*` is *exact* as a functor of triangulated categories.  No
  conditional form of this clause was available at all:
  `Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift` is an instance under the
  binder.
* `derivedPullback_isTriangulated_of_isMorphismOfSites`: **`Lf^*` carries a distinguished
  triangle to a distinguished triangle.**
* `derivedPullbackComparison_isIso_of_kFlat_of_flat` and
  `derivedPullbackComparison_isIso_of_boundedAbove_of_flat`: **`Lf^* K^• = f^* K^•`**, in the
  form of invertibility of the canonical comparison, for a K-flat complex with flat terms and
  for a bounded above complex of flat modules.

## Implementation notes

*The `haveI`s in the statements are proof-irrelevant.*
`CategoryTheory.Functor.HasLeftDerivedFunctor` is a `Prop`, so seating it in the statement of the
three results that mention
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback` or
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison` — both of
which need it to be written down at all — adds no data and no hypothesis.  It is spelled `haveI`
rather than `letI` for that reason, and by proof irrelevance the functor is the same whichever
witness is supplied.

*The morphism-of-sites hypothesis is the source's, not an addition.*
`AlgebraicGeometry.RingedToposSiteHom` presents the geometric morphism by a continuous functor
between the underlying sites and asks only for continuity; left exactness of `f^{-1}` is not a
field of it, and `hmos : f.u.IsMorphismOfSites Y.J X.J` is what makes `f` a morphism of ringed
topoi in the source's sense.  Every result in this chain carries it.

*Universes.*  `RingedTopos.{u, u, u}`, inherited from the results applied and narrowed there, not
here.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06XN](https://stacks.math.columbia.edu/tag/06XN)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.RingedToposDerivedPullback

namespace Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

include hmos in
/-- **Tag 06YY, compatibility with shifts.**  `Lf^*` commutes with the shift functors of the two
derived categories.  Together with `derivedPullback_isTriangulated_of_isMorphismOfSites` this is
the assertion that `Lf^*` is *exact* as a functor of triangulated categories.

This is `Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift` with its instance
binder discharged; that instance never needed the exactness clause, only the existence of the
derived functor. -/
@[instance_reducible, stacks 06YY "compatibility with shifts, for a morphism of ringed topoi
presented by a morphism of the underlying sites, at RingedTopos.{u, u, u}"]
def derivedPullbackCommShift :
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
    (derivedPullback f).CommShift ℤ :=
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
  derivedPullback_commShift f

include hmos in
/-- **Tag 06YY, exactness.**  `Lf^*` is an exact functor of triangulated categories: it carries a
distinguished triangle of `D(O')` to a distinguished triangle of `D(O)`.

This is `Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated` with both of
its inputs discharged — the exactness clause by `pullbackInvertsQuasiIso_isKFlat` and the
instance binder by `hasLeftDerivedFunctor_pullbackOnHomotopy`. -/
@[stacks 06YY "exactness, for a morphism of ringed topoi presented by a morphism of the
underlying sites, at RingedTopos.{u, u, u}"]
theorem derivedPullback_isTriangulated_of_isMorphismOfSites :
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
    (derivedPullback f).IsTriangulated :=
  have := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
  derivedPullback_isTriangulated f (pullbackInvertsQuasiIso_isKFlat f hmos)

include hmos in
/-- **Tag 06YY, the computation `Lf^* K^• = f^* K^•`.**  The canonical comparison
`Lf^* K^• ⟶ f^* K^•` is invertible at a K-flat complex `K^•` of `O'`-modules with flat terms: the
derived pullback of such a complex is computed by degreewise pullback.

This is
`Stacks.Sheaves.RingedToposDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat_of_flat`
with both of its inputs discharged.  Both hypotheses on `K^•` are the source's, and both are
used: they are the two clauses of the resolving class
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat`. -/
@[stacks 06YY "computation on K-flat complexes with flat terms, for a morphism of ringed topoi
presented by a morphism of the underlying sites, at RingedTopos.{u, u, u}"]
theorem derivedPullbackComparison_isIso_of_kFlat_of_flat
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
    IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  have := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
  isIso_derivedPullbackComparison_app_of_kFlat_of_flat f
    (pullbackInvertsQuasiIso_isKFlat f hmos) K hK hflat

include hmos in
/-- **Tag 06YY, the computation on a bounded above complex of flat modules.**  A bounded above
complex of flat `O'`-modules is K-flat by Tag 06YQ, so the canonical comparison is invertible
there too.  This is the "in particular" of the source's statement.

This is `isIso_derivedPullbackComparison_app_of_boundedAbove_of_flat` of
`Stacks.Sheaves.RingedToposDerivedPullback` with both of its inputs discharged. -/
@[stacks 06YY "computation on bounded above complexes of flat modules, for a morphism of ringed
topoi presented by a morphism of the underlying sites, at RingedTopos.{u, u, u}"]
theorem derivedPullbackComparison_isIso_of_boundedAbove_of_flat
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hbound : ∃ n : ℤ, K.IsStrictlyLE n)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
    IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  have := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
  isIso_derivedPullbackComparison_app_of_boundedAbove_of_flat f
    (pullbackInvertsQuasiIso_isKFlat f hmos) K hbound hflat

end Stacks.Cohomology.DerivedPullbackOnRingedTopoi

end
