module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationMap

/-!
# Derived stalks detect isomorphisms

A morphism of the unbounded derived category `D(Z_étale)` of abelian sheaves on the small étale
site of a scheme `Z` is an isomorphism as soon as its derived stalks at all geometric points are.
This is the derived form of Tag 03PU used in the proof of Tag 0GJU, and it discharges the
hypothesis `AlgebraicGeometry.HasDerivedStalkConservativity` of
`AlgebraicGeometry.isIso_pullback_cospecializationUnit`.

## Main results

* `AlgebraicGeometry.hasDerivedStalkConservativity` — the proposition
  `AlgebraicGeometry.HasDerivedStalkConservativity` holds: derived stalks at geometric points
  detect isomorphisms in `D(Z_étale)`.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 0GJU](https://stacks.math.columbia.edu/tag/0GJU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- `AlgebraicGeometry.HasDerivedStalkConservativity` holds: **derived stalks at geometric points
detect isomorphisms in `D(Z_étale)`.** A morphism `φ` of the unbounded derived category of abelian
sheaves on the small étale site of `Z` whose derived stalk at every geometric point of `Z` is an
isomorphism is an isomorphism.

The stalk functors are exact, so the derived stalk of `φ` computes, in each degree, the stalk of
the morphism of cohomology sheaves `H^n(φ)`; the geometric points form a conservative family of
points of the small étale site, so each `H^n(φ)` is an isomorphism, and a morphism of the derived
category inducing isomorphisms on all cohomology objects is an isomorphism. -/
theorem _root_.AlgebraicGeometry.hasDerivedStalkConservativity :
    HasDerivedStalkConservativity.{u} := by
  intro Z M N φ h
  rw [DerivedCategory.isIso_iff]
  intro n
  refine (isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun z => ?_
  have := h z
  exact (NatIso.isIso_map_iff
    (Functor.mapDerivedCategoryHomologyFunctorIso (smallEtaleStalkAb z.hom) n) φ).mp
      (by rw [Functor.comp_map]; infer_instance)

end Stacks.EtaleCohomology
