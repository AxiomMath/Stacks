module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation

/-!
# Absolute Noetherian approximation satisfying the standing convention

A Noetherian approximation of a presheaf on the big fppf site of `Spec ℤ` whose inverse system
satisfies `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.

## Main definitions

* `AlgebraicGeometry.Space.HasConventionalNoetherianApproximation`: a Noetherian approximation of
  a presheaf on the big fppf site of `Spec ℤ` whose inverse system satisfies
  `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.

## Main results

* `AlgebraicGeometry.Space.HasConventionalNoetherianApproximation.hasNoetherianApproximation`:
  such an approximation is a Noetherian approximation.
* `AlgebraicGeometry.Space.HasConventionalNoetherianApproximation.ofIso`: such an approximation
  transports along an isomorphism of presheaves.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- `X` has a Noetherian approximation over `Spec ℤ` whose inverse system satisfies
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. -/
def HasConventionalNoetherianApproximation
    (X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X,
    letI := A.preorder; letI := A.nonempty; letI := A.isDirected
    SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ A.diagram

variable {B hZ}

/-- A conventional Noetherian approximation is a Noetherian approximation. -/
theorem HasConventionalNoetherianApproximation.hasNoetherianApproximation
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (h : HasConventionalNoetherianApproximation B hZ X) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X :=
  let ⟨A, _⟩ := h; ⟨A⟩

/-- A conventional Noetherian approximation transports along an isomorphism; the inverse system
is unchanged. -/
theorem HasConventionalNoetherianApproximation.ofIso
    {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (h : HasConventionalNoetherianApproximation B hZ X) (e : X ≅ Y) :
    HasConventionalNoetherianApproximation B hZ Y :=
  let ⟨A, hA⟩ := h; ⟨A.ofIso e, hA⟩

end AlgebraicGeometry.Space

end
