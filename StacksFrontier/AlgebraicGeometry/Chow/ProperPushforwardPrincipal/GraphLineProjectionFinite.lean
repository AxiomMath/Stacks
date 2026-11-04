module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.GenericallyFinite
public import
  StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineDeltaDimension

/-!
# A proper dominant morphism of curves is finite, and the graph projection is finite

Let `C = (S, δ)` be a Chow situation whose dimension function vanishes identically and let `P`
and `Y` be integral schemes locally of finite type over `S`, both of delta-dimension one — two
curves over the base. This file shows that a proper dominant morphism `q : Y ⟶ P` over `S` is
**finite**, and applies that to the second projection `q : Y ⟶ ℙ¹_S` out of the graph closure of
Stacks 02RQ.

Every fibre of `q` is finite:

* every point of `P` other than the generic point has codimension one. The relative dimension of
  such a point is at most `0` because the delta-dimension is one, and at least `0` because the
  dimension function of the base vanishes and a transcendence degree is nonnegative; so it is
  exactly `0`, and that is equivalent to codimension one (Stacks 02RK,
  `Stacks.Chow.relativeDimension_eq_sub_one_iff_coheight_eq_one`). Over such a point the relative
  dimension on the fibre is constant, so no two of its points specialize to one another, and the
  fibre is finite by `Stacks.Chow.finite_preimage_singleton_of_specializes_imp_eq`;
* the fibre over the generic point of `P` is the single generic point of `Y`, because any other
  point of `Y` has relative dimension at most `0` while a point over the generic point of `P` has
  relative dimension at least `1`.

A morphism locally of finite type and quasi-compact with finite fibres is locally quasi-finite
(`AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton`), and a proper locally
quasi-finite morphism is finite (`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`).

## Main results

* `Stacks.Chow.eq_genericPoint_of_mem_genericFibre` — the fibre of a dominant morphism of curves
  over the generic point is the generic point.
* `Stacks.Chow.coheight_eq_one_of_ne_genericPoint` — every non-generic point of a curve over the
  base has codimension one.
* `Stacks.Chow.finite_preimage_singleton_of_ne_genericPoint` — the fibres over the non-generic
  points are finite.
* `Stacks.Chow.isFinite_of_isProper_of_isDominant_of_schemeDeltaDimension_eq_one` — **a proper
  dominant morphism between curves over the base is finite.**
* `Stacks.Chow.isFinite_graphLineProjection` — **the second projection out of the graph closure of
  Stacks 02RQ is finite** when it is dominant.

## Implementation notes

The statement is about an arbitrary target curve `P` rather than about `ℙ¹_S`, because nothing in
the argument is special to the projective line: what is used is that `P` is an integral scheme of
delta-dimension one over the base. The projective line enters only through
`Stacks.Chow.schemeDeltaDimension_relativeProjectiveLine_eq_one`, which supplies its
delta-dimension, and through `Stacks.Chow.isIntegral_relativeProjectiveLine`.

Dominance of the graph projection is a hypothesis, exactly as in
`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_relativeProjectiveLine`: it is
the case distinction of the Stacks proof, whose other branch is
`Stacks.Chow.principalDivisorCycle_eq_zero_of_not_isDominant`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 02UP](https://stacks.math.columbia.edu/tag/02UP)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {P Y : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  [IsIntegral P] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral Y]

/-- The fibre of a dominant morphism of integral schemes of delta-dimension one over the generic
point of the target is the generic point of the source. -/
theorem eq_genericPoint_of_mem_genericFibre
    (hnP : schemeDeltaDimension C sP = (1 : EInt))
    (hnY : schemeDeltaDimension C sY = (1 : EInt))
    (q : Y ⟶ P) [LocallyOfFiniteType q] (hq : q ≫ sP = sY)
    {x : Y} (hx : q.base x = genericPoint P) : x = genericPoint Y := by
  by_contra hne
  have hle := relativeDimension_le_sub_one_of_ne_genericPoint C sY hnY hne
  have hP1 : relativeDimension C.dimensionFunction sP (genericPoint P) = 1 :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C sP).symm.trans hnP)
  have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sP q x
  rw [hq, hx, hP1] at hstep
  omega

/-- On an integral scheme of delta-dimension one over a base whose dimension function vanishes,
every point other than the generic point has codimension one. -/
theorem coheight_eq_one_of_ne_genericPoint (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    (hnP : schemeDeltaDimension C sP = (1 : EInt)) {y : P} (hy : y ≠ genericPoint P) :
    Order.coheight y = 1 := by
  rw [← relativeDimension_eq_sub_one_iff_coheight_eq_one C sP hnP y]
  have hle := relativeDimension_le_sub_one_of_ne_genericPoint C sP hnP hy
  have hge : 0 ≤ relativeDimension C.dimensionFunction sP y := by
    rw [relativeDimension, hδ]
    positivity
  omega

/-- The fibre of a proper dominant morphism of curves over the base above a point other than the
generic point is finite. -/
theorem finite_preimage_singleton_of_ne_genericPoint
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    (hnP : schemeDeltaDimension C sP = (1 : EInt))
    (hnY : schemeDeltaDimension C sY = (1 : EInt))
    (q : Y ⟶ P) [IsProper q] [IsDominant q] (hq : q ≫ sP = sY)
    {y : P} (hy : y ≠ genericPoint P) : (q.base ⁻¹' {y}).Finite := by
  have hco : Order.coheight y = 1 := coheight_eq_one_of_ne_genericPoint C sP hδ hnP hy
  refine finite_preimage_singleton_of_specializes_imp_eq q y fun x x' hx hx' hspec ↦ ?_
  by_contra hne
  have hlt := (deltaDimensionFunction C sY).strictAnti_specializes hspec hne
  rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply,
    relativeDimension_eq_sub_one_of_mem_fibre C sY sP hnY hnP q hq hco hx,
    relativeDimension_eq_sub_one_of_mem_fibre C sY sP hnY hnP q hq hco hx'] at hlt
  omega

/-- **A proper dominant morphism between two curves over the base is finite.** -/
theorem isFinite_of_isProper_of_isDominant_of_schemeDeltaDimension_eq_one
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    (hnP : schemeDeltaDimension C sP = (1 : EInt))
    (hnY : schemeDeltaDimension C sY = (1 : EInt))
    (q : Y ⟶ P) [IsProper q] [IsDominant q] (hq : q ≫ sP = sY) :
    IsFinite q := by
  have hqf : LocallyQuasiFinite q := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro y
    obtain rfl | hy := eq_or_ne y (genericPoint P)
    · exact (Set.finite_singleton _).subset fun x hx ↦
        eq_genericPoint_of_mem_genericFibre C sP sY hnP hnY q hq hx
    · exact finite_preimage_singleton_of_ne_genericPoint C sP sY hδ hnP hnY q hq hy
  exact IsFinite.of_isProper_of_locallyQuasiFinite q

/-- **The second projection out of the graph closure of Stacks 02RQ is finite**, when it is
dominant and the curve `X` lies over the spectrum of a field. -/
theorem isFinite_graphLineProjection (k : Type u) [Field k] (C : ChowSituation.{u})
    [IsIntegral C.S] (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [IsProper sX] [IsIntegral X]
    (U : X.Opens) (g : (Γ(X, U))ˣ)
    (hYint : IsIntegral (graphClosure sX U ↑g))
    (hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g))
    (hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (1 : EInt))
    (hdom : IsDominant (graphLineProjection sX U ↑g)) :
    IsFinite (graphLineProjection sX U ↑g) := by
  have := hYint
  have := hYft
  have := hdom
  exact isFinite_of_isProper_of_isDominant_of_schemeDeltaDimension_eq_one C
    (relativeProjectiveLine C.S ↘ C.S) (graphBaseMorphism sX U ↑g) hδ
    (schemeDeltaDimension_relativeProjectiveLine_eq_one k C hS hδ) hYdim
    (graphLineProjection sX U ↑g) (graphLineProjection_comp sX U ↑g)

end Stacks.Chow

end
