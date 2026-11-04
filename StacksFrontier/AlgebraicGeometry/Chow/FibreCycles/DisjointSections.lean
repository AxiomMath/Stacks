module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.SectionRange

/-!
# The zero and the infinity section are disjoint closed immersions

The two distinguished points `0` and `∞` of `ℙ¹_ℤ` are the origins of the two affine charts of
the gluing of Tag 01JE, and the charts overlap exactly where the coordinate is invertible. Hence
neither point lies in the other's chart: their images in `ℙ¹_ℤ` are disjoint. Both points are
moreover closed immersions of `Spec ℤ` into `ℙ¹_ℤ`, being immersions with closed image.

A constant section of `X ×_S ℙ¹_S ⟶ X` is the base change of the corresponding integral point
along the projection to `ℙ¹_ℤ`, so both properties pass to the zero and the infinity section of
a family: they are closed immersions with disjoint images. Disjointness is what makes the two
fibres `W₀` and `W_∞` of Stacks Tag 02S4 disjoint divisors on `W`, and closedness is what lets
either fibre be regarded as a closed subscheme of `X`.

## Main results

* `Stacks.Chow.disjoint_range_integralZeroSection_integralInfinitySection`: the two
  distinguished points of `ℙ¹_ℤ` have disjoint images.
* `Stacks.Chow.isClosedImmersion_integralZeroSection` and
  `Stacks.Chow.isClosedImmersion_integralInfinitySection`: they are closed immersions.
* `Stacks.Chow.isClosedImmersion_constantSection`: a constant section attached to an integral
  point which is a closed immersion is itself a closed immersion; hence
  `Stacks.Chow.isClosedImmersion_zeroSection` and
  `Stacks.Chow.isClosedImmersion_infinitySection`.
* `Stacks.Chow.disjoint_range_zeroSection_infinitySection`: the zero and the infinity section
  of `X ×_S ℙ¹_S ⟶ X` have disjoint images, so no point of the family lies on both
  (`Stacks.Chow.zeroSection_ne_infinitySection`).

## Implementation notes

Disjointness in `ℙ¹_ℤ` reuses `Stacks.Chow.notMem_range_ι_of_X_mem`: the point `0` is the image
under the first chart of a point at which the coordinate vanishes, so it misses the second
chart entirely, while `∞` lies in the second chart by construction. Disjointness for a family
is then a disjointness of preimages under `Stacks.Chow.projectiveLineProjection`, by
`Stacks.Chow.range_constantSection`.

Closedness of the two integral points is `Stacks.Chow.isClosed_range_integralZeroSection`;
combined with `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion` — the composite of the
isomorphism of terminal schemes, the closed immersion cutting out the origin of the affine line
and the open immersion of a chart is a preimmersion — it gives the closed immersion property.
That property is stable under base change, and
`Stacks.Chow.isPullback_constantSection` exhibits a constant section as a base change.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The two charts of the projective line are indexed by distinct elements. -/
theorem projectiveLineXIndex_ne_projectiveLineYIndex (k : Type u) [CommRing k] :
    projectiveLineXIndex k ≠ projectiveLineYIndex k :=
  fun h => Bool.false_ne_true (congrArg ULift.down h)

/-- The two distinguished points `0` and `∞` of `ℙ¹_ℤ` have disjoint images: `0` lies in the
first chart at a point where the coordinate vanishes, hence outside the second chart, whereas
`∞` lies in the second chart. -/
theorem disjoint_range_integralZeroSection_integralInfinitySection :
    Disjoint (Set.range (integralZeroSection.{u}))
      (Set.range (integralInfinitySection.{u})) := by
  rw [Set.disjoint_left]
  rintro p hp0 hpinf
  rw [range_integralZeroSection] at hp0
  rw [range_integralInfinitySection] at hpinf
  obtain ⟨x, hx, rfl⟩ := hp0
  obtain ⟨y, -, hy⟩ := hpinf
  exact notMem_range_ι_of_X_mem (ULift.{u} ℤ) _ _
    (projectiveLineXIndex_ne_projectiveLineYIndex (ULift.{u} ℤ)) x
    (X_mem_of_mem_range_specMap_evalRingHom_zero hx) ⟨y, hy⟩

/-- The origin of an affine-line chart is a closed immersion: evaluation at zero is a surjective
ring map. -/
public instance isClosedImmersion_specMap_evalRingHom_zero :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.evalRingHom (0 : ULift.{u} ℤ)))) :=
  IsClosedImmersion.spec_of_surjective _ fun a => ⟨Polynomial.C a, by simp⟩

/-- The point `0` of `ℙ¹_ℤ` is a closed immersion of `Spec ℤ`. -/
public instance isClosedImmersion_integralZeroSection :
    IsClosedImmersion (integralZeroSection.{u}) := by
  have : IsIso (AlgebraicGeometry.specULiftZIsTerminal.from (⊤_ Scheme.{u})) :=
    isIso_of_isTerminal terminalIsTerminal AlgebraicGeometry.specULiftZIsTerminal _
  have : IsPreimmersion (integralZeroSection.{u}) := by
    rw [integralZeroSection]
    infer_instance
  exact IsClosedImmersion.of_isPreimmersion _ isClosed_range_integralZeroSection

/-- The point `∞` of `ℙ¹_ℤ` is a closed immersion of `Spec ℤ`. -/
public instance isClosedImmersion_integralInfinitySection :
    IsClosedImmersion (integralInfinitySection.{u}) := by
  have : IsIso (AlgebraicGeometry.specULiftZIsTerminal.from (⊤_ Scheme.{u})) :=
    isIso_of_isTerminal terminalIsTerminal AlgebraicGeometry.specULiftZIsTerminal _
  have : IsPreimmersion (integralInfinitySection.{u}) := by
    rw [integralInfinitySection]
    infer_instance
  exact IsClosedImmersion.of_isPreimmersion _ isClosed_range_integralInfinitySection

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The constant section of `X ×_S ℙ¹_S ⟶ X` attached to an integral point which is a closed
immersion is again a closed immersion, being its base change along the projection to
`ℙ¹_ℤ`. -/
theorem isClosedImmersion_constantSection
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) [IsClosedImmersion e] :
    IsClosedImmersion (constantSection f e) :=
  MorphismProperty.of_isPullback (isPullback_constantSection f e).flip inferInstance

/-- The zero section of `X ×_S ℙ¹_S ⟶ X` is a closed immersion. -/
public instance isClosedImmersion_zeroSection : IsClosedImmersion (zeroSection f) :=
  isClosedImmersion_constantSection f _

/-- The infinity section of `X ×_S ℙ¹_S ⟶ X` is a closed immersion. -/
public instance isClosedImmersion_infinitySection : IsClosedImmersion (infinitySection f) :=
  isClosedImmersion_constantSection f _

/-- The zero and the infinity section of `X ×_S ℙ¹_S ⟶ X` have disjoint images: both are
preimages under the projection to `ℙ¹_ℤ` of the images of the two distinguished points, which
are disjoint. -/
theorem disjoint_range_zeroSection_infinitySection :
    Disjoint (Set.range (zeroSection f)) (Set.range (infinitySection f)) := by
  rw [zeroSection, infinitySection, range_constantSection, range_constantSection]
  exact disjoint_range_integralZeroSection_integralInfinitySection.preimage _

/-- No point of `X ×_S ℙ¹_S` lies both on the zero section and on the infinity section. -/
theorem zeroSection_ne_infinitySection (x y : X) :
    zeroSection f x ≠ infinitySection f y := fun h =>
  Set.disjoint_left.mp (disjoint_range_zeroSection_infinitySection f) ⟨x, rfl⟩ ⟨y, h.symm⟩

end Stacks.Chow

end
