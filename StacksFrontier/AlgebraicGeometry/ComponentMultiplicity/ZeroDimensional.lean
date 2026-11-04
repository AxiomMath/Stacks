module

public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.ZeroDimensionalSupport
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Formula
public import StacksFrontier.AlgebraicGeometry.EulerCharDirectSum.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The component formula of Stacks Tag 0AYW in dimension zero

On a scheme of dimension at most zero the index set of the sum in Stacks Tag 0AYW is empty, so the
component formula asserts that the degree of a finite locally free sheaf vanishes. This holds for
an invertible sheaf on a scheme proper over a field, and for a finite locally free sheaf of rank
`r` isomorphic to the direct sum of `r` copies of the structure sheaf.

## Main results

In the namespace `AlgebraicGeometry`:

* `curveDegree_eq_zero_of_iso_biprodPow`: a finite locally free sheaf of rank `r` isomorphic to
  `𝒪_X^{⊞ r}` has degree zero.
* `invertibleCurveDegree_eq_zero_of_discreteTopology`: an invertible sheaf on a scheme with
  discrete underlying space has degree zero.

In the namespace `Stacks.AlgebraicGeometry.ComponentDegrees`:

* `genericPointsOne_eq_empty_of_topologicalKrullDim_le_zero`: a scheme of dimension at most zero
  has no one-dimensional irreducible component, so every sum of the shape appearing in Tag 0AYW
  vanishes there (`finsum_genericPointsOne_eq_zero_of_topologicalKrullDim_le_zero`).
* `discreteTopology_of_isProper_of_topologicalKrullDim_le_zero`: a scheme of dimension at most
  zero proper over a field has discrete underlying space.
* `curveDegree_eq_finsum_componentDegree_of_isInvertible_of_topologicalKrullDim_le_zero` and
  `exists_curveDegree_eq_finsum_of_isInvertible_of_topologicalKrullDim_le_zero`: the component
  formula, and its existential form, for an invertible sheaf on a scheme of dimension at most
  zero.
* `curveDegree_eq_finsum_componentDegree_of_topologicalKrullDim_le_zero` and
  `exists_curveDegree_eq_finsum_of_topologicalKrullDim_le_zero`: the same two statements for a
  finite locally free sheaf of rank `r` isomorphic to `𝒪_X^{⊞ r}`.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A finite locally free sheaf of rank `r` isomorphic to `𝒪_X^{⊞ r}` has degree zero.** -/
public theorem curveDegree_eq_zero_of_iso_biprodPow (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hX : topologicalKrullDim X ≤ 1) (E : X.Modules)
    (rank : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (e : E ≅ Scheme.Modules.biprodPow (X := X) (SheafOfModules.unit X.ringCatSheaf) rank) :
    curveDegree k f hX E rank = 0 := by
  rw [curveDegree, sub_eq_zero, mul_finsum]
  refine finsum_congr fun n => ?_
  rw [finrank_cohomologyOverField_eq_of_iso k f e n,
    finrank_cohomologyOverField_biprodPow k f
      (X := X) (SheafOfModules.unit X.ringCatSheaf) rank n]
  push_cast
  ring

/-- **An invertible sheaf on a scheme with discrete underlying space has degree zero.** -/
public theorem invertibleCurveDegree_eq_zero_of_discreteTopology (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [DiscreteTopology (X : Type u)]
    (hX : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    invertibleCurveDegree k f hX L = 0 := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology X L
  exact invertibleCurveDegree_eq_zero_of_iso_unit k f hX L e

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ComponentDegrees

/-- **A scheme of dimension at most zero has no one-dimensional irreducible component.** -/
public theorem genericPointsOne_eq_empty_of_topologicalKrullDim_le_zero (X : Scheme.{u})
    (hX0 : topologicalKrullDim X ≤ 0) : genericPointsOne X = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false, mem_genericPointsOne_iff, not_and]
  intro _ hx
  have hle : topologicalKrullDim (closure ({x} : Set X)) ≤ topologicalKrullDim X :=
    topologicalKrullDim_subspace_le _ _
  rw [hx] at hle
  exact absurd (hle.trans hX0) (by decide)

/-- The index set of the sum of Stacks Tag 0AYW is empty on a scheme of dimension at most
zero. -/
public theorem isEmpty_genericPointsOne_of_topologicalKrullDim_le_zero (X : Scheme.{u})
    (hX0 : topologicalKrullDim X ≤ 0) : IsEmpty (genericPointsOne X) := by
  rw [genericPointsOne_eq_empty_of_topologicalKrullDim_le_zero X hX0]
  exact Set.isEmpty_coe_sort.mpr rfl

/-- **On a scheme of dimension at most zero every sum of the shape appearing in Stacks Tag 0AYW
vanishes.** -/
public theorem finsum_genericPointsOne_eq_zero_of_topologicalKrullDim_le_zero (X : Scheme.{u})
    (hX0 : topologicalKrullDim X ≤ 0) (g : genericPointsOne X → ℤ) :
    ∑ᶠ ξ : genericPointsOne X, g ξ = 0 :=
  have := isEmpty_genericPointsOne_of_topologicalKrullDim_le_zero X hX0
  finsum_of_isEmpty g

/-- **A scheme of dimension at most zero that is proper over a field has discrete underlying
space.** -/
@[ega "0 14.1.9" "necessity, special case"]
public theorem discreteTopology_of_isProper_of_topologicalKrullDim_le_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hX0 : topologicalKrullDim X ≤ 0) :
    DiscreteTopology (X : Type u) :=
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k f
  _root_.AlgebraicGeometry.discrete_of_noetherian_topologicalKrullDim_le_zero hX0

/-- **The component formula of Stacks Tag 0AYW for an invertible sheaf on a scheme of dimension
at most zero.** -/
public theorem curveDegree_eq_finsum_componentDegree_of_isInvertible_of_topologicalKrullDim_le_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (hX0 : topologicalKrullDim X ≤ 0) (L : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    curveDegree k f hX L 1 =
      ∑ᶠ ξ : genericPointsOne X,
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX L 1 ξ := by
  rw [finsum_genericPointsOne_eq_zero_of_topologicalKrullDim_le_zero X hX0
    (fun ξ => (componentMultiplicity X ξ : ℤ) * componentDegree k f hX L 1 ξ)]
  have := discreteTopology_of_isProper_of_topologicalKrullDim_le_zero k f hX0
  rw [← _root_.AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree_one k f hX L]
  exact _root_.AlgebraicGeometry.invertibleCurveDegree_eq_zero_of_discreteTopology k f hX L

/-- **The conclusion of Stacks Tag 0AYW for an invertible sheaf on a scheme of dimension at most
zero**, in the existential form the tag states: the components are proper of dimension at most
one, the pullbacks of the sheaf to them are finite locally free of rank one, and the component
formula holds. -/
public theorem exists_curveDegree_eq_finsum_of_isInvertible_of_topologicalKrullDim_le_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (hX0 : topologicalKrullDim X ≤ 0) (L : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ (hproper : ∀ ξ : genericPointsOne X, IsProper (reducedComponentι X ξ ≫ f))
      (hdimC : ∀ ξ : genericPointsOne X, topologicalKrullDim (reducedComponent X ξ) ≤ 1)
      (hrank : ∀ ξ : genericPointsOne X,
        _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj L) 1),
      curveDegree k f hX L 1 =
        ∑ᶠ ξ : genericPointsOne X,
          (componentMultiplicity X ξ : ℤ) *
            @curveDegree k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
              (hproper ξ) (hdimC ξ)
              ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj L) 1 (hrank ξ) :=
  (exists_curveDegree_eq_finsum_iff k f hX L 1).2
    (curveDegree_eq_finsum_componentDegree_of_isInvertible_of_topologicalKrullDim_le_zero
      k f hX hX0 L)

/-- **The component formula of Stacks Tag 0AYW for a scheme of dimension at most zero carrying a
globally free sheaf.** -/
public theorem curveDegree_eq_finsum_componentDegree_of_topologicalKrullDim_le_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (hX0 : topologicalKrullDim X ≤ 0) (E : X.Modules)
    (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (e : E ≅ _root_.AlgebraicGeometry.Scheme.Modules.biprodPow (X := X)
      (_root_.SheafOfModules.unit X.ringCatSheaf) rank) :
    curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X,
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ := by
  rw [finsum_genericPointsOne_eq_zero_of_topologicalKrullDim_le_zero X hX0
    (fun ξ => (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ)]
  exact _root_.AlgebraicGeometry.curveDegree_eq_zero_of_iso_biprodPow k f hX E rank e

/-- **The conclusion of Stacks Tag 0AYW for a scheme of dimension at most zero carrying a
globally free sheaf**, in the existential form the tag states. -/
public theorem exists_curveDegree_eq_finsum_of_topologicalKrullDim_le_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (hX0 : topologicalKrullDim X ≤ 0) (E : X.Modules)
    (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (e : E ≅ _root_.AlgebraicGeometry.Scheme.Modules.biprodPow (X := X)
      (_root_.SheafOfModules.unit X.ringCatSheaf) rank) :
    ∃ (hproper : ∀ ξ : genericPointsOne X, IsProper (reducedComponentι X ξ ≫ f))
      (hdimC : ∀ ξ : genericPointsOne X, topologicalKrullDim (reducedComponent X ξ) ≤ 1)
      (hrank : ∀ ξ : genericPointsOne X,
        _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank),
      curveDegree k f hX E rank =
        ∑ᶠ ξ : genericPointsOne X,
          (componentMultiplicity X ξ : ℤ) *
            @curveDegree k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
              (hproper ξ) (hdimC ξ)
              ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank (hrank ξ) :=
  (exists_curveDegree_eq_finsum_iff k f hX E rank).2
    (curveDegree_eq_finsum_componentDegree_of_topologicalKrullDim_le_zero k f hX hX0 E rank e)

end Stacks.AlgebraicGeometry.ComponentDegrees

end
