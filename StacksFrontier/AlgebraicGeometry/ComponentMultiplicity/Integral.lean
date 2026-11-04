module

public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Reduced
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# The component formula of Stacks Tag 0AYW on an integral scheme of dimension one

On an integral scheme of dimension one the sum in the component formula of Stacks Tag 0AYW has
a single term, of weight one, and the single component is the whole scheme. This file proves the
formula there; it is the base case of the induction in the proof of the tag, at `e = 0` and on
one component.

## Main results

* `Stacks.AlgebraicGeometry.ComponentDegrees.curveDegree_eq_finsum_componentDegree_of_isIntegral`:
  for an integral scheme of dimension one the degree of a finite locally free sheaf is the
  multiplicity-weighted sum of its degrees on the one-dimensional components.
* `Stacks.AlgebraicGeometry.ComponentDegrees.exists_curveDegree_eq_finsum_of_isIntegral`: the
  same, in the existential form the tag states.

## Implementation notes

The dimension enters twice and in two shapes. `AlgebraicGeometry.curveDegree` takes
`topologicalKrullDim X ≤ 1`, which is what the tag assumes; the index set is a singleton only
when the dimension is *exactly* one, which is what
`Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne_eq_singleton` needs. Both are
hypotheses: on a zero-dimensional integral scheme the index set is empty and the formula is a
different statement.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.AlgebraicGeometry.ComponentDegrees

universe u

/-- **The component formula of Stacks Tag 0AYW for an integral scheme of dimension one**: the
degree of a finite locally free sheaf `E` is the multiplicity-weighted sum of its degrees on the
one-dimensional components. -/
theorem curveDegree_eq_finsum_componentDegree_of_isIntegral (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (hX1 : topologicalKrullDim (X : Type u) = 1)
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X,
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ := by
  rw [finsum_componentDegree_of_isIntegral X hX1 (componentDegree k f hX E rank)]
  set ξ : genericPointsOne X :=
    ⟨genericPoint (X : Type u), genericPoint_self_mem_genericPointsOne X hX1⟩
  have : IsIso (reducedComponentι X ξ) := isIso_reducedComponentι_of_isIntegral X ξ rfl
  have : IsProper (reducedComponentι X ξ ≫ f) := isProper_reducedComponentι_comp k f ξ
  have : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) rank :=
    isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ E rank
  exact (curveDegree_pullback k (reducedComponentι X ξ) f
    (topologicalKrullDim_reducedComponent_le X hX ξ) hX E rank).symm

/-- **The conclusion of Stacks Tag 0AYW for an integral scheme of dimension one**, in the
existential form the tag states: the properness, dimension and rank conditions on the components
hold, and the component formula holds with respect to them. -/
theorem exists_curveDegree_eq_finsum_of_isIntegral (k : Type u) [Field k] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (hX1 : topologicalKrullDim (X : Type u) = 1)
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
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
    (curveDegree_eq_finsum_componentDegree_of_isIntegral k f hX hX1 E rank)

end Stacks.AlgebraicGeometry.ComponentDegrees

end
