module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentRealised

/-!
# Morphisms of modifications at closed points are determined by their base changes

Let `X` be a decent algebraic space over a scheme `S`, let `x₁, …, xₙ ∈ |X|` be the chosen
closed points and let `(Uᵢ, uᵢ) → (X, xᵢ)` be the chosen elementary étale neighborhoods, that is
a term `D : ClosedPointNeighborhoods B S hS n`. A morphism of modifications of `X` away from
`{x₁, …, xₙ}` is determined by its base changes to the `Uᵢ`. This is the faithfulness of the
functor

`F : C_{X, {x₁, …, xₙ}} ⟶ C_{U₁, u₁} × … × C_{Uₙ, uₙ}`

of Stacks 0BHA, stated for morphisms of the slice category over `X`.

Two morphisms of modifications of `X` away from `{x₁, …, xₙ}` agree over `X ∖ {x₁, …, xₙ}`,
where both the source and the target of the morphism become the open subspace itself: the base
change of each of them along the inclusion of that open subspace is a *terminal* object of the
slice category, so there is only one morphism between them. The family
`{X ∖ {x₁, …, xₙ}, U₁, …, Uₙ}` is an fppf covering family of `X`
(`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isFppfCovering_coverHom`), so its base change
along the structure morphism of the source is an fppf covering of the source by Stacks 03Y9, and
an fppf covering can be cancelled on the left against a morphism into an algebraic space, which
is the separatedness half of the fppf case of Stacks 04P2
(`AlgebraicGeometry.Space.hom_ext_of_isFppfCovering`).

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.pullback_map_openAwayFromPoints_eq`: two
  morphisms of modifications agree after base change to `X ∖ {x₁, …, xₙ}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.hom_ext_of_pullback_map_eq`: a morphism of
  modifications is determined by its base changes to the chosen neighborhoods.

## References

* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
* [Stacks Project, Tag 03Y9](https://stacks.math.columbia.edu/tag/03Y9)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- **Two morphisms of modifications of `X` away from `{x₁, …, xₙ}` agree over
`X ∖ {x₁, …, xₙ}`.**  The base change of the target along the inclusion of that open subspace is
terminal in the slice category, both the source and the target becoming the open subspace
itself, so there is only one morphism between the base changes. -/
theorem pullback_map_openAwayFromPoints_eq {M N : D.modificationsAwayFromPoints}
    (f g : M.obj ⟶ N.obj) :
    (Over.pullback D.openAwayFromPoints.ι).map f =
      (Over.pullback D.openAwayFromPoints.ι).map g :=
  (isTerminalPullbackObj B S hS D.openAwayFromPoints.ι N.obj N.property.2).hom_ext _ _

/-- **A morphism of modifications of `X` away from `{x₁, …, xₙ}` is determined by its base
changes to the chosen neighborhoods.** -/
theorem hom_ext_of_pullback_map_eq {M N : D.modificationsAwayFromPoints}
    (f g : M.obj ⟶ N.obj)
    (h : ∀ i, (Over.pullback (D.toSpaceHom i).hom).map f =
      (Over.pullback (D.toSpaceHom i).hom).map g) : f = g := by
  have hcov := isFppfCovering_fibreProduct B S hS D.coverSpace D.coverSpaceHom
    (ObjectProperty.homMk M.obj.hom :
      (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space)
    D.isFppfCovering_coverHom
  refine Over.OverMorphism.ext (hom_ext_of_isFppfCovering B S hS _ _ hcov
    N.property.1.isSheaf fun j => ?_)
  refine (pullback_map_left_comp_fst _ f).symm.trans
    ((congrArg (Over.Hom.left · ≫ _) ?_).trans (pullback_map_left_comp_fst _ g))
  rcases j with _ | i
  exacts [D.pullback_map_openAwayFromPoints_eq f g, h i]

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
