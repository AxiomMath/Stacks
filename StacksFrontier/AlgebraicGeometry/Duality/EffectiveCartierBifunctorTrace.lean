module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.ExactSupportPushforwardModelComparison

/-!
# The comparison morphism of Tag 0B4B in the bifunctor model of Tag 0A77

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`
and normal sheaf `𝒩 = i^* 𝒪_X(D)`.  The canonical comparison morphism
`𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` of [Stacks, Tag 0B4B] is pinned down by being the adjunct of the
morphism `Ri_*(𝒩[-1]) ⟶ 𝒪_X` that the normal extension class determines
(`Stacks.Divisors.normalShiftToDerivedSheafHomExactSupport_adjunct`), that is, by its
compatibility with the counit of [Stacks, Tag 0A76].

This file reads that compatibility in the *bifunctor* model of [Stacks, Tag 0A77]: pushing the
comparison morphism forward, identifying `Ri_* R ℰom(𝒪_D, 𝒪_X)` with
`R ℰom_{𝒪_X}(Ri_* 𝒪_D, 𝒪_X)` and composing with the trace of that model returns the morphism
determined by the normal extension class.  It is the form in which the comparison morphism meets
a comparison of distinguished triangles: the triangle obtained from the ideal sequence
`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` by contravariant exactness of the derived internal Hom
([Stacks, Tag 08I0]) has `R ℰom_{𝒪_X}(Ri_* 𝒪_D, 𝒪_X)` as its first term, and that is the
bifunctor, not the total right derived functor of `ℰom_{𝒪_X}(i_* 𝒪_D, -)`.

## Main results

* `Stacks.Divisors.pushforward_normalShiftToDerivedSheafHomExactSupport_comp`: the comparison
  morphism of [Stacks, Tag 0B4B], pushed forward, carried into the bifunctor model of
  [Stacks, Tag 0A77] and composed with that model's trace, is
  `Stacks.Divisors.pushforwardNormalShiftToStructureSheaf`.

## Implementation notes

The statement is the componentwise counit compatibility
`…derivedSheafHomExactSupportPushforwardNatIso_hom_app_comp_bifunctorEvaluationAtOne` followed
by `Adjunction.homEquiv_symm_apply`, which turns the adjunct into the pushforward of the
comparison morphism composed with the counit.

The bifunctor model brings the global locally small instances
`SheafOfModules.hasDerivedCategory` and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`
into scope, and they would be preferred to `HasDerivedCategory.standard`. Here
`HasDerivedCategory.standard` is pinned at a priority that outranks them, and the objects of the
statement are taken from the types of the declarations being composed rather than written out,
so that no instance is resolved afresh.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **The comparison morphism of [Stacks, Tag 0B4B], read in the bifunctor model of
[Stacks, Tag 0A77].** Pushing the comparison morphism `𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` forward,
identifying `Ri_* R ℰom(𝒪_D, 𝒪_X)` with `R ℰom_{𝒪_X}(Ri_* 𝒪_D, 𝒪_X)` by the bifunctor model of
[Stacks, Tag 0A77] and composing with the trace
`R ℰom_{𝒪_X}(Ri_* 𝒪_D, -) ⟶ 𝟭` of that model returns the morphism `Ri_*(𝒩[-1]) ⟶ 𝒪_X`
determined by the normal extension class.

This is the counit compatibility of the bifunctor model read at the structure sheaf, together
with the fact that the comparison morphism is an adjunct. -/
theorem pushforward_normalShiftToDerivedSheafHomExactSupport_comp :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
          (normalShiftToDerivedSheafHomExactSupport D) ≫
        (closedQuotient D).derivedSheafHomExactSupportPushforwardNatIso.hom.app _ ≫
          (closedQuotient D).bifunctorEvaluationAtOne.app _ =
      pushforwardNormalShiftToStructureSheaf D := by
  have hA := (closedQuotient D)
    |>.derivedSheafHomExactSupportPushforwardNatIso_hom_app_comp_bifunctorEvaluationAtOne
      ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))
  have hc := Adjunction.homEquiv_symm_apply
    (closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction _ _
    (normalShiftToDerivedSheafHomExactSupport D)
  rw [hA, ← hc]
  exact normalShiftToDerivedSheafHomExactSupport_adjunct D

end Stacks.Divisors

end
