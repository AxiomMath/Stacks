module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ClosedSections

/-!
# The image of a constant section of a family of projective lines

For `f : X ⟶ S`, the family `X ×_S ℙ¹_S` is also the product of `X` with `ℙ¹_ℤ` over the
terminal scheme, so it carries a projection to `ℙ¹_ℤ`. The constant section attached to an
integral point `e` of `ℙ¹_ℤ` is then the base change of `e` along that projection: the square

```
X ------------> X ×_S ℙ¹_S
|                   |
v                   v
Spec ℤ ----e----> ℙ¹_ℤ
```

is cartesian. Consequently the image of the constant section is the preimage of the image of
`e`, and is closed as soon as the image of `e` is. Applied to the two distinguished points of
`ℙ¹_ℤ`, this says that the zero and the infinity section of `X ×_S ℙ¹_S ⟶ X` have closed
image, which is what makes "the subscheme is not contained in the image of the section" the
right nondegeneracy hypothesis in Stacks Tag 02S4.

## Main definitions

* `Stacks.Chow.projectiveLineProjection`: the projection `X ×_S ℙ¹_S ⟶ ℙ¹_ℤ`.

## Main results

* `Stacks.Chow.isPullback_constantSection`: the square above is cartesian.
* `Stacks.Chow.range_constantSection`: the image of a constant section is the preimage of the
  image of the integral point under the projection to `ℙ¹_ℤ`.
* `Stacks.Chow.isClosed_range_zeroSection` and
  `Stacks.Chow.isClosed_range_infinitySection`: the images of the two distinguished sections
  are closed.

## Implementation notes

The cartesian square is obtained by cancellation, not by a hand-built cone: pasting the two
defining pullback squares of `X ×_S ℙ¹_S` and of `ℙ¹_S` exhibits `X ×_S ℙ¹_S` as the product of
`X` and `ℙ¹_ℤ` over the terminal scheme, and `CategoryTheory.IsPullback.of_right` then peels
off the right-hand square. The outer square needed for the cancellation is cartesian for a
cheap reason: its top edge is `constantSection f e ≫ pullback.fst`, which is the identity, and
its bottom edge is a morphism between terminal schemes, hence also an isomorphism.

The image statement follows because `CategoryTheory.IsPullback.isoPullback` identifies `X` with
the canonical pullback, whose first projection has image the preimage of the image of `e` by
`AlgebraicGeometry.Scheme.Pullback.range_fst`.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ))

/-- The structure morphism of `ℙ¹_S` is the first projection of the defining pullback. -/
theorem relativeProjectiveLine_over_hom (S : Scheme.{u}) :
    (relativeProjectiveLine S ↘ S) =
      pullback.fst (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))) := rfl

/-- The projection of the family `X ×_S ℙ¹_S` to the projective line over the integers. -/
public def projectiveLineProjection :
    projectiveLineProduct f ⟶ projectiveLine (ULift.{u} ℤ) :=
  pullback.snd f (relativeProjectiveLine S ↘ S) ≫
    pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ)))

/-- A constant section composed with the projection to `ℙ¹_ℤ` is the chosen integral point. -/
theorem constantSection_comp_projection :
    constantSection f e ≫ projectiveLineProjection f = terminal.from X ≫ e := by
  rw [projectiveLineProjection, ← Category.assoc]
  simp only [constantSection, pullback.lift_snd]

/-- The family `X ×_S ℙ¹_S` is the product of `X` and `ℙ¹_ℤ` over the terminal scheme. -/
theorem isPullback_projectiveLineProjection :
    IsPullback (pullback.fst f (relativeProjectiveLine S ↘ S))
      (projectiveLineProjection f) (f ≫ terminal.from S)
      (terminal.from (projectiveLine (ULift.{u} ℤ))) := by
  rw [projectiveLineProjection]
  refine (IsPullback.of_hasPullback f (relativeProjectiveLine S ↘ S)).paste_vert ?_
  rw [relativeProjectiveLine_over_hom]
  exact IsPullback.of_hasPullback _ _

/-- A constant section of `X ×_S ℙ¹_S ⟶ X` is the base change of the corresponding integral
point of `ℙ¹_ℤ` along the projection to `ℙ¹_ℤ`. -/
theorem isPullback_constantSection :
    IsPullback (constantSection f e) (terminal.from X) (projectiveLineProjection f) e := by
  refine IsPullback.of_right ?_ (constantSection_comp_projection f e)
    (isPullback_projectiveLineProjection f)
  rw [constantSection_comp_fst, show e ≫ terminal.from (projectiveLine (ULift.{u} ℤ))
    = 𝟙 (⊤_ Scheme.{u}) from terminal.hom_ext _ _]
  exact IsPullback.of_horiz_isIso ⟨terminal.hom_ext _ _⟩

/-- The image of a constant section is the preimage of the image of the integral point. -/
theorem range_constantSection :
    Set.range (constantSection f e) = projectiveLineProjection f ⁻¹' Set.range e := by
  have h := isPullback_constantSection f e
  rw [show constantSection f e = h.isoPullback.hom ≫
      pullback.fst (projectiveLineProjection f) e from h.isoPullback_hom_fst.symm,
    range_comp_scheme, (surjective_of_isIso h.isoPullback.hom).range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]

/-- A constant section attached to an integral point with closed image has closed image. -/
theorem isClosed_range_constantSection (he : IsClosed (Set.range e)) :
    IsClosed (Set.range (constantSection f e)) := by
  rw [range_constantSection]
  exact he.preimage (projectiveLineProjection f).continuous

/-- The image of the zero section is closed. -/
theorem isClosed_range_zeroSection : IsClosed (Set.range (zeroSection f)) :=
  isClosed_range_constantSection f _ isClosed_range_integralZeroSection

/-- The image of the infinity section is closed. -/
theorem isClosed_range_infinitySection : IsClosed (Set.range (infinitySection f)) :=
  isClosed_range_constantSection f _ isClosed_range_integralInfinitySection

end Stacks.Chow

end
