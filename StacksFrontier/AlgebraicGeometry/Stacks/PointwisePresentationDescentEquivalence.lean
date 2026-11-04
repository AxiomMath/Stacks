module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescentEquivalence.Cocycle
public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescentEquivalence.Gluing
public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescentEquivalence.Equiv

/-!
# Quasi-coherent modules on a pointwise groupoid presentation and on the groupoid

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and `[U/_pR]` its pointwise groupoid
fibration, whose objects over `T` are the `T`-points of `U` and whose arrows over `T` are the
`T`-points of `R`. The descent functor `QCoh(𝒪_{[U/_pR]}) ⥤ QCoh(U, R, s, t, c)`,
`𝒩 ↦ (ι^*𝒩|_{U_étale}, α)`, is an equivalence, and so is the descent functor of every fully
faithful 1-morphism `F : [U/_pR] ⥤ 𝒳` which covers `𝒳`.

Given a quasi-coherent module `(𝒢, α)` on the groupoid, there is a quasi-coherent module `M` on
`𝒮_U` with `M|_{U_étale} ≅ 𝒢` and a morphism `β : t^*M ⟶ s^*M` on `𝒮_R` attached to `α`; the
pair `(M, β)` is a descent datum for the pointwise groupoid fibration
(`AlgebraicGeometry.Stack.PointwiseDescentDatum`), and the module glued from it is a
quasi-coherent module on `[U/_pR]` whose image under the descent functor is `(𝒢, α)`.

## Main definitions

* `AlgebraicGeometry.Stack.pointwiseDatumOfQuasicoherent`: the descent datum `(M, β)` attached
  to a quasi-coherent module on the groupoid.
* `AlgebraicGeometry.Stack.pointwiseSheafOfQuasicoherent`: the quasi-coherent module on
  `[U/_pR]` glued from it.
* `AlgebraicGeometry.Stack.pointwiseIdDescentFunctorObjIso`: its image under the descent functor
  is the given module on the groupoid.

## Main results

* `AlgebraicGeometry.Stack.descComp_descentMorphism_identity` and
  `AlgebraicGeometry.Stack.descComp_descentMorphism_compose`: the unit and cocycle conditions of
  the descent morphism, pointwise.
* `AlgebraicGeometry.Stack.isEquivalence_pointwiseQuasicoherentDescentFunctor_id`: the descent
  functor of `[U/_pR]` is an equivalence.
* `AlgebraicGeometry.Stack.isEquivalence_pointwiseQuasicoherentDescentFunctor`: the descent
  functor of a fully faithful 1-morphism `F : [U/_pR] ⥤ 𝒳` covering `𝒳` is an equivalence.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 06WR](https://stacks.math.columbia.edu/tag/06WR)
-/
