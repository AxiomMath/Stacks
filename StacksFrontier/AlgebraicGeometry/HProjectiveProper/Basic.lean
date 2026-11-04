module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# H-projective morphisms are proper, and a curve is not both affine and H-projective

A morphism `f : X ⟶ S` is *H-projective* when it factors as a closed immersion
`i : X ⟶ ℙⁿ_S` followed by the structure morphism of relative projective space, for some `n`.
Such an `f` is proper, and a curve over a field is never both affine and H-projective over that
field. H-projectivity is expressed by the data `i`, `IsClosedImmersion i` and
`i ≫ (ℙⁿ_S ↘ S) = f`.

## Main results

* `AlgebraicGeometry.projectiveSpaceOver_eq_projectiveSpace`: the two constructions
  `AlgebraicGeometry.projectiveSpaceOver` and `AlgebraicGeometry.ProjectiveSpace` of relative
  projective space agree.
* `AlgebraicGeometry.projectiveSpaceOver_isProper`: `ℙⁿ_S ⟶ S` is proper.
* `AlgebraicGeometry.isProper_of_isClosedImmersion_projectiveSpaceOver`: an H-projective
  morphism is proper.
* `AlgebraicGeometry.not_isAffine_of_isCurve_of_isClosedImmersion_projectiveSpaceOver`: a curve
  over a field that is H-projective over that field is not affine.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (n : ℕ) (S : Scheme.{u})

/-- The two integral models `AlgebraicGeometry.projectiveSpaceAtUniverse` and
`AlgebraicGeometry.ProjectiveSpaceZ` of projective space agree: both are `Proj` of the
polynomial ring in `n + 1` variables over `ULift ℤ`, graded by total degree. -/
public theorem projectiveSpaceAtUniverse_eq_projectiveSpaceZ :
    projectiveSpaceAtUniverse.{u} n = ProjectiveSpaceZ.{u} n :=
  rfl

/-- The two constructions `AlgebraicGeometry.projectiveSpaceOver` and
`AlgebraicGeometry.ProjectiveSpace` of relative projective space agree: both are the base change
of the integral model along the structure morphism of the base. -/
public theorem projectiveSpaceOver_eq_projectiveSpace :
    projectiveSpaceOver n S = ProjectiveSpace n S :=
  rfl

/-- The two constructions of relative projective space have the same structure morphism: both
are the first pullback projection. -/
public theorem projectiveSpaceOver_over_eq :
    (projectiveSpaceOver n S ↘ S) = (ProjectiveSpace n S ↘ S) :=
  rfl

/-- Relative projective space `AlgebraicGeometry.projectiveSpaceOver n S` is proper over `S`. -/
public instance projectiveSpaceOver_isProper : IsProper (projectiveSpaceOver n S ↘ S) :=
  ProjectiveSpace.instIsProperOver n S

variable {n S}

/-- If `f` factors as a closed immersion into relative projective space followed by its
structure morphism, then `f` is proper. -/
public theorem isProper_of_isClosedImmersion_projectiveSpaceOver {X : Scheme.{u}} {f : X ⟶ S}
    (i : X ⟶ projectiveSpaceOver n S) [IsClosedImmersion i]
    (h : i ≫ (projectiveSpaceOver n S ↘ S) = f) : IsProper f :=
  h ▸ inferInstance

/-- A curve over a field `k` which admits a closed immersion into relative projective space
over `k`, compatibly with its structure morphism, is not affine. -/
public theorem not_isAffine_of_isCurve_of_isClosedImmersion_projectiveSpaceOver (k : Type u)
    [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsCurve k f]
    (i : X ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion i]
    (h : i ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f) : ¬ IsAffine X :=
  have : IsProper f := isProper_of_isClosedImmersion_projectiveSpaceOver i h
  not_isAffine_of_isCurve k f

end AlgebraicGeometry

end
