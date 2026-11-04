module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Formula
public import StacksCore.Tactic.StacksAttribute

/-!
# Components of a reduced scheme have multiplicity one

The multiplicity of a one-dimensional irreducible component of a scheme, in the sense of Stacks
Tag 0AYW, is the length of the local ring at its generic point. On a reduced scheme that local
ring is a field, so every component has multiplicity one and the component formula of Tag 0AYW
loses its weights. This is the base case `e = 0` of the induction in the source proof of that
tag, where `X` equals its own reduction.

This file connects the two halves that were proved separately and could not meet:
`AlgebraicGeometry.length_stalk_eq_one_of_isMax` is stated for a point maximal in the
specialization order, and `Stacks.AlgebraicGeometry.ComponentDegrees.isMax_of_mem_genericPoints`
says a generic point is such a point. It also records what the component formula says when `X`
is in addition irreducible: the index set is a singleton and the whole sum is the degree on the
single component.

## Main results

* `Stacks.AlgebraicGeometry.ComponentDegrees.componentMultiplicity_eq_one_of_isReduced`: on a
  reduced scheme every one-dimensional component has multiplicity one.
* `curveDegree_eq_finsum_componentDegree_iff_of_isReduced`, in the same namespace: for reduced
  `X` the conclusion of Tag 0AYW is equivalent to the unweighted formula
  `deg(ℰ) = ∑ᶠ ξ, deg(ℰ|_{C(ξ)})`.
* `Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne_eq_singleton`: an irreducible
  scheme of dimension one has exactly one one-dimensional component, indexed by its generic
  point.
* `Stacks.AlgebraicGeometry.ComponentDegrees.isIso_reducedComponentι_of_isIntegral`: on an
  integral scheme the closed immersion of the component indexed by the generic point is an
  isomorphism.
* `Stacks.AlgebraicGeometry.ComponentDegrees.finsum_componentDegree_of_isIntegral`: for an
  integral scheme of dimension one the sum of Tag 0AYW has one term, of weight one.

## Implementation notes

`componentMultiplicity` is valued in `ℕ`, obtained from the length in `ℕ∞` by `ENat.toNat`, so
the multiplicity-one statement needs no finiteness hypothesis: `(1 : ℕ∞).toNat = 1` outright.
In particular neither properness nor a dimension bound appears in
`componentMultiplicity_eq_one_of_isReduced`, where
`Stacks.AlgebraicGeometry.ComponentDegrees.componentMultiplicity_cast` would have required both.

`isIso_reducedComponentι_of_isIntegral` is proved by applying
`Stacks.AlgebraicGeometry.ComponentDegrees.exists_isIso_hom_to_reducedComponent` to the identity
of `X`, which is a closed immersion with integral source whose generic point is the index. The
morphism it produces is a two-sided inverse of the component's closed immersion, by
`CategoryTheory.IsIso.inv_eq_of_hom_inv_id`.

**What is not proved here, and where the base case is finished.** Tag 0AYW for an integral `X` of
dimension one is not proved in this file and nothing here carries the attribute. By
`finsum_componentDegree_of_isIntegral` its two sides are `curveDegree k f hX E rank` and
`curveDegree` of the pullback of `ℰ` along `reducedComponentι X ξ` over
`reducedComponentι X ξ ≫ f`; by `isIso_reducedComponentι_of_isIntegral` that morphism is an
isomorphism. So the base case is exactly the statement that `AlgebraicGeometry.curveDegree` is
invariant under an isomorphism of schemes over the base — the companion, across an isomorphism of
*schemes*, of `AlgebraicGeometry.curveDegree_eq_of_iso`, which is invariance across an isomorphism
of *modules* on one scheme. That companion is `AlgebraicGeometry.curveDegree_pullback` of
`StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree`, and
`Stacks.AlgebraicGeometry.ComponentDegrees.curveDegree_eq_finsum_componentDegree_of_isIntegral` of
`StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Integral` is the base case assembled from it
and the two halves above.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.AlgebraicGeometry.ComponentDegrees

universe u

/-- **On a reduced scheme every one-dimensional component has multiplicity one.** The local ring
at a generic point of a reduced scheme is a field, so its length over itself is one. -/
theorem componentMultiplicity_eq_one_of_isReduced {X : Scheme.{u}} [IsReduced X]
    (ξ : genericPointsOne X) : componentMultiplicity X ξ = 1 := by
  have h : Module.length (X.presheaf.stalk ξ.1) (X.presheaf.stalk ξ.1) = 1 :=
    length_stalk_eq_one_of_isMax
      (isMax_of_mem_genericPoints ξ.1 (mem_genericPointsOne_iff.mp ξ.2).1)
  simp [componentMultiplicity, h]

/-- On a reduced scheme the multiplicity weights in the sum of Stacks Tag 0AYW are all one. -/
theorem finsum_componentMultiplicity_mul_of_isReduced {X : Scheme.{u}} [IsReduced X]
    (g : genericPointsOne X → ℤ) :
    ∑ᶠ ξ : genericPointsOne X, (componentMultiplicity X ξ : ℤ) * g ξ =
      ∑ᶠ ξ : genericPointsOne X, g ξ :=
  finsum_congr fun ξ => by rw [componentMultiplicity_eq_one_of_isReduced ξ]; simp

/-- **For a reduced scheme the component formula of Stacks Tag 0AYW is unweighted.** Combined
with `Stacks.AlgebraicGeometry.ComponentDegrees.exists_curveDegree_eq_finsum_iff`, the whole
conclusion of the tag is equivalent to `deg(ℰ) = ∑ᶠ ξ, deg(ℰ|_{C(ξ)})`. -/
theorem curveDegree_eq_finsum_componentDegree_iff_of_isReduced (k : Type u) [Field k]
    {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    (curveDegree k f hX E rank =
        ∑ᶠ ξ : genericPointsOne X,
          (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ) ↔
      curveDegree k f hX E rank =
        ∑ᶠ ξ : genericPointsOne X, componentDegree k f hX E rank ξ := by
  rw [finsum_componentMultiplicity_mul_of_isReduced (componentDegree k f hX E rank)]

/-- An irreducible scheme of dimension one has exactly one one-dimensional irreducible
component, indexed by its generic point. -/
theorem genericPointsOne_eq_singleton (X : Scheme.{u}) [IrreducibleSpace X]
    (hX : topologicalKrullDim (X : Type u) = 1) :
    genericPointsOne X = {genericPoint (X : Type u)} := by
  have hgp : genericPoints (X : Type u) = {genericPoint (X : Type u)} := genericPoints_eq_singleton
  have hcl : closure ({genericPoint (X : Type u)} : Set X) = Set.univ := by
    simp [genericPoint_closure (α := (X : Type u))]
  have hdimcl : topologicalKrullDim (closure ({genericPoint (X : Type u)} : Set X)) = 1 := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ (X : Type u)).isHomeomorph).trans hX
  ext x
  rw [mem_genericPointsOne_iff, hgp, Set.mem_singleton_iff]
  refine ⟨fun h => h.1, ?_⟩
  rintro rfl
  exact ⟨rfl, hdimcl⟩

/-- The generic point of an irreducible scheme of dimension one indexes a one-dimensional
component. -/
theorem genericPoint_self_mem_genericPointsOne (X : Scheme.{u}) [IrreducibleSpace X]
    (hX : topologicalKrullDim (X : Type u) = 1) :
    genericPoint (X : Type u) ∈ genericPointsOne X := by
  rw [genericPointsOne_eq_singleton X hX]
  rfl

/-- On an irreducible scheme of dimension one there is nothing to index but the generic point. -/
theorem eq_genericPoint_of_mem_genericPointsOne (X : Scheme.{u}) [IrreducibleSpace X]
    (hX : topologicalKrullDim (X : Type u) = 1) (ξ : genericPointsOne X) :
    ξ.1 = genericPoint (X : Type u) :=
  Set.eq_of_mem_singleton ((genericPointsOne_eq_singleton X hX).subset ξ.2)

/-- **On an integral scheme the closed immersion of the component at the generic point is an
isomorphism.** The scheme is its own reduced one-dimensional component. -/
theorem isIso_reducedComponentι_of_isIntegral (X : Scheme.{u}) [IsIntegral X]
    (ξ : genericPointsOne X) (hξ : ξ.1 = genericPoint (X : Type u)) :
    IsIso (reducedComponentι X ξ) := by
  obtain ⟨ψ, hψ, hfac⟩ :=
    exists_isIso_hom_to_reducedComponent (𝟙 X) ξ (by simpa using hξ.symm)
  have h : CategoryTheory.inv ψ = reducedComponentι X ξ := IsIso.inv_eq_of_hom_inv_id hfac
  rw [← h]
  infer_instance

/-- **For an integral scheme of dimension one the sum of Stacks Tag 0AYW has a single term, of
weight one.** Its value is the degree on the component indexed by the generic point. -/
theorem finsum_componentDegree_of_isIntegral (X : Scheme.{u}) [IsIntegral X]
    (hX : topologicalKrullDim (X : Type u) = 1) (g : genericPointsOne X → ℤ) :
    ∑ᶠ ξ : genericPointsOne X, (componentMultiplicity X ξ : ℤ) * g ξ =
      g ⟨genericPoint (X : Type u), genericPoint_self_mem_genericPointsOne X hX⟩ := by
  have huniq : ∀ ξ : genericPointsOne X,
      ξ = ⟨genericPoint (X : Type u), genericPoint_self_mem_genericPointsOne X hX⟩ :=
    fun ξ => Subtype.ext (eq_genericPoint_of_mem_genericPointsOne X hX ξ)
  rw [finsum_eq_single _ ⟨genericPoint (X : Type u), genericPoint_self_mem_genericPointsOne X hX⟩
    (fun x hx => absurd (huniq x) hx)]
  rw [componentMultiplicity_eq_one_of_isReduced]
  simp

end Stacks.AlgebraicGeometry.ComponentDegrees

end
