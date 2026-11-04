module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCanonical
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackFlatClosed

/-!
# Open and closed conditions on `Coh_{X/Y}` along base change of the standing data

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces, the standing data of
Stacks 08KB, let `g : Y' ⟶ Y` be a morphism of algebraic spaces and let `X' = X ×_Y Y'`.  By
Stacks 08LP the square

`Coh_{X'/Y'} ⟶ Coh_{X/Y}`,  `𝒮_{Y'} ⟶ 𝒮_Y`

is 2-cartesian; its top row sends an object `(T, 𝓕)` of `Coh_{X'/Y'}` to the same test scheme `T`,
read over `Y`, with the module `𝓕` read on `X_T ≅ X'_T`.  Consequently, if a condition `Q` on the
objects of `Coh_{X/Y}` cuts out an open and closed (or a flat closed) substack, then so does the
condition "the image in `Coh_{X/Y}` satisfies `Q`" on `Coh_{X'/Y'}`: the substack it cuts out is
the base change `Coh_{X'/Y'} ×_{Coh_{X/Y}} Coh^Q`, and it is represented on an object over `T` by
the same subscheme of `T`.

This is the cartesian square through which the proof of Stacks 0DNE concludes: after absolute
Noetherian approximation, `Coh_{X/B} ⟶ Coh_{X_i/Spec(Λ_i)}` is such a top row, and the substack
`Coh^P_{X/B}` is the pullback of `Coh^P_{X_i/Spec(Λ_i)}`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition.baseChange`: an open and
  closed condition on `Coh_{X/Y}` pulls back to an open and closed condition on `Coh_{X'/Y'}`.
* `AlgebraicGeometry.Space.CoherentSituation.IsFlatClosedCondition.baseChange`: the same for flat
  closed conditions.

## Implementation notes

The top row of the square is `AlgebraicGeometry.Space.CoherentSituation.baseChangeObject'` and
`AlgebraicGeometry.Space.CoherentSituation.baseChangeHom'` at the base-change stability
`AlgebraicGeometry.Space.modulePullbackStabilityOfFinitePresentation`.  It does not change test
schemes nor their morphisms, which is why the representing subschemes can be taken unchanged.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {Y' : AlgebraicSpaces B S hS}

namespace CoherentSituation

/-- The image in `Coh_{X/Y}` of an object of `Coh_{X'/Y'}` has the same test scheme. -/
@[simp]
theorem testScheme_baseChangeObject (g : Y' ⟶ D.Y) (A : CoherentObject (D.baseChange g)) :
    (D.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A).testScheme =
      A.testScheme :=
  rfl

/-- The image in `Coh_{X/Y}` of a morphism of `Coh_{X'/Y'}` has the same morphism of test
schemes. -/
@[simp]
theorem baseScheme_baseChangeHom (g : Y' ⟶ D.Y) {A' A : CoherentObject (D.baseChange g)}
    (φ : CoherentHom A' A) :
    (D.baseChangeHom' (modulePullbackStabilityOfFinitePresentation B S hS) g φ).baseScheme =
      φ.baseScheme :=
  rfl

/-- **Open and closed substacks pull back along the base change of the standing data.**  If a
condition `Q` on the objects of `Coh_{X/Y}` cuts out an open and closed substack, then for every
`g : Y' ⟶ Y` the condition "the image in `Coh_{X/Y}` satisfies `Q`" cuts out an open and closed
substack of `Coh_{X'/Y'}`, `X' = X ×_Y Y'`; on an object over `T` it is represented by the
subscheme of `T` which represents `Q` on the image of that object. -/
theorem IsOpenAndClosedCondition.baseChange {Q : CoherentObject D → Prop}
    (hQ : IsOpenAndClosedCondition D Q) (g : Y' ⟶ D.Y) :
    IsOpenAndClosedCondition (D.baseChange g)
      fun A =>
        Q (D.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A) := by
  intro A
  obtain ⟨U, hU, h⟩ :=
    hQ (D.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A)
  exact ⟨U, hU, fun A' φ =>
    h _ (D.baseChangeHom' (modulePullbackStabilityOfFinitePresentation B S hS) g φ)⟩

/-- **Flat closed substacks pull back along the base change of the standing data.**  If a
condition `Q` on the objects of `Coh_{X/Y}` cuts out a flat closed substack, then for every
`g : Y' ⟶ Y` the condition "the image in `Coh_{X/Y}` satisfies `Q`" cuts out a flat closed
substack of `Coh_{X'/Y'}`, `X' = X ×_Y Y'`. -/
theorem IsFlatClosedCondition.baseChange {Q : CoherentObject D → Prop}
    (hQ : IsFlatClosedCondition D Q) (g : Y' ⟶ D.Y) :
    IsFlatClosedCondition (D.baseChange g)
      fun A =>
        Q (D.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A) := by
  intro A
  obtain ⟨V, s, hs, hflat, h⟩ :=
    hQ (D.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A)
  exact ⟨V, s, hs, hflat, fun A' φ =>
    h _ (D.baseChangeHom' (modulePullbackStabilityOfFinitePresentation B S hS) g φ)⟩

/-- **Open and closed conditions are transported along the base change of the standing data.**
If a condition `Q'` on the objects of `Coh_{X'/Y'}` agrees, object by object, with an open and
closed condition `Q` on `Coh_{X/Y}` evaluated at the image, then `Q'` is open and closed.  This is
the form in which the cartesian square of the proof of Stacks 0DNE is used: there `Q'` and `Q` are
the numerical conditions of Situation 0DNC on the two sides. -/
theorem IsOpenAndClosedCondition.of_baseChange {Q : CoherentObject D → Prop}
    (hQ : IsOpenAndClosedCondition D Q) (g : Y' ⟶ D.Y) {Q' : CoherentObject (D.baseChange g) → Prop}
    (hQQ' : ∀ A, Q' A ↔
      Q (D.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A)) :
    IsOpenAndClosedCondition (D.baseChange g) Q' := by
  have hfun : Q' = fun A =>
      Q (D.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A) :=
    funext fun A => propext (hQQ' A)
  exact hfun ▸ hQ.baseChange g

end CoherentSituation

end AlgebraicGeometry.Space

end
