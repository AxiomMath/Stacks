module

public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject

/-!
# The direct-summand step of Stacks 0FPD, conclusion (a), on a ringed space

Let `(X, O_X)` be a ringed space, let `M` be an object of `D(O_X)` with a left dual `N` for the
derived tensor product of Stacks 0FPB — an exact pairing, Categories, Definition 0FFP — and
suppose the coevaluation `η : O_X ⟶ M ⊗^L N` factors through `K ⊗^L N` along a map
`f : K ⟶ M`. If `K` is perfect then `M` is perfect.

This is the step the source of Stacks 0FPD announces as "we are going to use the following
argument several times": a subcomplex `K^• ⊆ M^•` containing the finitely many sections
occurring in `η(1)` receives the coevaluation, and *"since the composition of the upper row is
the identity on `M` we conclude that `M` is a direct summand of `K` in `D(O_X)`"*. Both halves
of that conclusion are now available and are composed here.

Nothing below is a clause of a tag; this is a step of the proof of Stacks 0FPD, whose conclusion
(a) is `Stacks.Cohomology.LeftDualPerfect.isPerfect_of_exactPairing`. No hypothesis below stands
in for a theorem: `f`, `coev` and the factorization are morphism data.

## Main results

* `Stacks.Cohomology.LeftDualPerfect.isPerfect_of_coevaluationFactors`: the statement above.

## What this is made of

* `CategoryTheory.ExactPairing.retractOfCoevaluationFactors`
  (`StacksFrontier.CategoryTheory.Monoidal.Rigid`) turns the factorization into a
  `CategoryTheory.Retract M K`. It is pure monoidal yoga — one of the two triangle identities and
  the unitors — and assumes nothing about `D(O_X)`.
* `Stacks.Cohomology.PerfectDirectSummands.isPerfect_of_retract`
  (`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject`) carries
  perfectness back along the retract. It is Tag 08CS strengthened from a biproduct to a retract,
  using that a retract in a pretriangulated category is a direct summand.

The construction of `K`, `f` and `coev` near a point is
`Stacks.Cohomology.LeftDualPerfect.exists_local_retract`.

## Implementation notes

The monoidal structure `Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory` of
Stacks 0FPB is not an instance, so the whole statement sits under one `letI` and the pairing, the
factoring map and the factorization are taken in binders after it. That is cheaper than seating
the structure separately in each binder's type and keeps the elaborator from re-deriving it.

The spelling is the one of
`StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects`, where Stacks 0FPG lives and
where this clause's consumer
`Stacks.Cohomology.InvertibleDerived.hasInvertibleModuleDecomposition_of_isInvertibleObject`
sits: objects in `Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf` for a ringed space
`X`, perfectness in the Tag 08CM spelling `Stacks.Cohomology.PerfectComplexes.IsPerfect`, and the
pairing hypothesis of Stacks 0FPD supplied there by
`Stacks.Cohomology.InvertibleDerived.exists_exactPairing_of_isInvertibleObject`.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.MonoidalDerived

universe u d d'

namespace Stacks.Cohomology.LeftDualPerfect

/-- **The direct-summand step of Stacks 0FPD, conclusion (a).** Let `N` be a left dual of `M` in
`D(O_X)` for the derived tensor product of Stacks 0FPB, and suppose the coevaluation of the
pairing factors as `coev ≫ f ▷ N = η_ M N` through `K ⊗^L N`, along a map `f : K ⟶ M`. If `K` is
perfect then `M` is perfect.

The factorization makes `M` a retract of `K` —
`CategoryTheory.ExactPairing.retractOfCoevaluationFactors`, which is the triangle identity
`(1 ⊗ ε) ∘ (η ⊗ 1) = id` read through the factorization — and a retract of a perfect object is
perfect, `Stacks.Cohomology.PerfectDirectSummands.isPerfect_of_retract`.

This is a step of the proof of Stacks 0FPD, conclusion (a), and carries no `@[stacks]`
attribute. -/
theorem isPerfect_of_coevaluationFactors (X : RingedSpace.{u, u})
    [inst : HasDerivedCategory.{d} (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf)]
    [∀ V : Opens X.carrier, HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict V.isOpenEmbedding))]
    (M N K : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} X inst K) :
    letI := derivedCategoryMonoidalCategory X
    ∀ [ExactPairing M N] (f : K ⟶ M)
      (coev : 𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf) ⟶ K ⊗ N),
      coev ≫ f ▷ N = η_ M N →
      @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} X inst M := by
  let : HasDerivedCategory.{d} (OXMod.{u, u} X) := inst
  let := derivedCategoryMonoidalCategory X
  intro _ f coev hcoev
  obtain ⟨i, r, h⟩ := ExactPairing.retractOfCoevaluationFactors f coev hcoev
  exact Stacks.Cohomology.PerfectDirectSummands.isPerfect_of_retract (X := X) i r h hK

end Stacks.Cohomology.LeftDualPerfect

end
