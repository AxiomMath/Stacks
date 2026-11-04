module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineIntegral
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.AffineLineIso

/-!
# The gluing relation of the relative projective line

The relative projective line `ℙ¹_S` of `Stacks.Chow.relativeProjectiveLine` is covered by the
two affine charts `Stacks.Chow.affineChart` and `Stacks.Chow.affineYChart`, both with source the
affine line `Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOver S`. This file
records the relation along which the two charts are glued: they agree on the *relative punctured
line* `Stacks.Chow.puncturedLineOver S`, and the two pullbacks of the affine coordinate
`Stacks.Chow.affineCoordinate` to it are inverse to each other, the first being `T` and the
second `T⁻¹`.

Everything here is the base change along the projection `𝔸¹_S ⟶ 𝔸¹_ℤ` of the corresponding
statement about `ℙ¹_ℤ`, which is `AlgebraicGeometry.isPullback_projectiveLineCharts`: the
punctured line `Spec ℤ[T, T⁻¹]` is the intersection of the two charts of `ℙ¹_ℤ`, the coordinate
of the first chart restricting to `T` and that of the second to `T⁻¹`.

## Main definitions

* `Stacks.Chow.puncturedLineOver` — the relative punctured line `S ×_{Spec ℤ} Spec ℤ[T, T⁻¹]`.
* `Stacks.Chow.puncturedChartOver` — its inclusion into `𝔸¹_S` with coordinate `T`.
* `Stacks.Chow.puncturedYChartOver` — its inclusion into `𝔸¹_S` with coordinate `T⁻¹`.
* `Stacks.Chow.puncturedLineOneSection` — the section of the punctured line through `T = 1`.

## Main results

* `Stacks.Chow.puncturedChartOver_comp_affineChart` — the two inclusions of the punctured line
  agree after composing with the two affine charts of `ℙ¹_S`.
* `Stacks.Chow.puncturedChartOver_appTop_affineCoordinate_mul` — the two pullbacks of the affine
  coordinate to the punctured line multiply to `1`.
* `Stacks.Chow.exists_puncturedComparison` — the packaged form of the gluing relation, for a
  consumer that needs only the existence of the comparison.

## Implementation notes

The source of `Stacks.Chow.puncturedChartOver` and `Stacks.Chow.puncturedYChartOver` is the same
scheme, exactly as the two affine charts of `ℙ¹_S` share their source: both inclusions of the
punctured line into `𝔸¹_ℤ` have source `Spec ℤ[T, T⁻¹]`, the second being the first precomposed
with the inversion `AlgebraicGeometry.projectiveLineInversionIso`.

Both inclusions are open immersions because both of their models over `ℤ` are, and
`AlgebraicGeometry.IsOpenImmersion` is stable under base change. Integrality of the punctured
line then follows from `AlgebraicGeometry.isIntegral_of_isOpenImmersion` together with
integrality of `𝔸¹_S`, once the punctured line is known to be nonempty; nonemptiness is
witnessed by the section through the point `T = 1`, the same point that
`Stacks.Chow.integralOneSection` uses to show that the two charts of `ℙ¹_ℤ` meet.

The name `AlgebraicGeometry.Spec` is written out in full throughout, because a root-level `Spec`
is in scope here through the transitive imports and the bare name is ambiguous.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The relative punctured line and its two inclusions into `𝔸¹_S` -/

/-- The relative punctured line `S ×_{Spec ℤ} Spec ℤ[T, T⁻¹]`, the open subscheme of `𝔸¹_S`
on which the affine coordinate is invertible. -/
abbrev puncturedLineOver (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S)
    (terminal.from (AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ)))))

/-- The inclusion of the relative punctured line into `𝔸¹_S` along which the affine coordinate
pulls back to `T`: the base change of `AlgebraicGeometry.projectiveLinePuncturedChart`. -/
def puncturedChartOver (S : Scheme.{u}) : puncturedLineOver S ⟶ affineLineOver S :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ projectiveLinePuncturedChart (ULift.{u} ℤ)) (terminal.hom_ext _ _)

/-- The inclusion of the relative punctured line into `𝔸¹_S` along which the affine coordinate
pulls back to `T⁻¹`: the base change of
`AlgebraicGeometry.projectiveLineOverlapInverseCoordinate`. -/
def puncturedYChartOver (S : Scheme.{u}) : puncturedLineOver S ⟶ affineLineOver S :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom
      (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom)) (terminal.hom_ext _ _)

/-- The first inclusion of the punctured line lies over `S`. -/
@[simp]
theorem puncturedChartOver_fst (S : Scheme.{u}) :
    puncturedChartOver S ≫ pullback.fst (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      pullback.fst (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ))))) :=
  pullback.lift_fst _ _ _

/-- On the second factor, the first inclusion of the punctured line is
`AlgebraicGeometry.projectiveLinePuncturedChart`. -/
@[simp]
theorem puncturedChartOver_snd (S : Scheme.{u}) :
    puncturedChartOver S ≫ pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      pullback.snd (terminal.from S)
          (terminal.from (AlgebraicGeometry.Spec
            (.of (LaurentPolynomial (ULift.{u} ℤ))))) ≫
        projectiveLinePuncturedChart (ULift.{u} ℤ) :=
  pullback.lift_snd _ _ _

/-- The second inclusion of the punctured line lies over `S`. -/
@[simp]
theorem puncturedYChartOver_fst (S : Scheme.{u}) :
    puncturedYChartOver S ≫ pullback.fst (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      pullback.fst (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ))))) :=
  pullback.lift_fst _ _ _

/-- On the second factor, the second inclusion of the punctured line is the inverse overlap
coordinate. -/
@[simp]
theorem puncturedYChartOver_snd (S : Scheme.{u}) :
    puncturedYChartOver S ≫ pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      pullback.snd (terminal.from S)
          (terminal.from (AlgebraicGeometry.Spec
            (.of (LaurentPolynomial (ULift.{u} ℤ))))) ≫
        Spec.map (CommRingCat.ofHom
          (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom) :=
  pullback.lift_snd _ _ _

/-! ### The commuting square -/

/-- **The two affine charts of `ℙ¹_S` agree on the punctured line.** -/
theorem puncturedChartOver_comp_affineChart (S : Scheme.{u}) :
    puncturedChartOver S ≫ affineChart S = puncturedYChartOver S ≫ affineYChart S := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc,
      show affineChart S ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveLine (ULift.{u} ℤ))) =
        pullback.fst (terminal.from S)
          (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))) from
        affineChart_comp S,
      show affineYChart S ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveLine (ULift.{u} ℤ))) =
        pullback.fst (terminal.from S)
          (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))) from
        affineYChart_comp S,
      puncturedChartOver_fst, puncturedYChartOver_fst]
  · rw [Category.assoc, Category.assoc, (isPullback_affineChart S).w,
      (isPullback_affineYChart S).w, ← Category.assoc, ← Category.assoc,
      puncturedChartOver_snd, puncturedYChartOver_snd, Category.assoc, Category.assoc,
      (isPullback_projectiveLineCharts (ULift.{u} ℤ)).w]

/-! ### Both inclusions are open immersions -/

/-- The inverse overlap coordinate defines an open immersion of affine schemes: it is the
inclusion of the punctured line precomposed with the inversion isomorphism. -/
theorem isOpenImmersion_specMap_projectiveLineOverlapInverseCoordinate
    (k : Type u) [CommRing k] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (projectiveLineOverlapInverseCoordinate k).toRingHom)) := by
  rw [← projectiveLineInversionIso_hom_comp_puncturedChart k]
  infer_instance

/-- A lift of the projection of the punctured line along a morphism `f` of the models over `ℤ`
is the base change of `f` along the projection of `𝔸¹_S` to `𝔸¹_ℤ`. -/
private theorem isPullback_of_fst_snd (S : Scheme.{u})
    (f : AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ))) ⟶
      AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))
    (g : puncturedLineOver S ⟶ affineLineOver S)
    (hfst : g ≫ pullback.fst (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      pullback.fst (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ))))))
    (hsnd : g ≫ pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      pullback.snd (terminal.from S)
          (terminal.from (AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ))))) ≫ f) :
    IsPullback g
      (pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ))))))
      (pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))))
      f := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (terminal.from S)
      (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ)))))) ?_
    hsnd (IsPullback.of_hasPullback _ _)
  rw [hfst, show f ≫ terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ)))) =
    terminal.from (AlgebraicGeometry.Spec
      (.of (LaurentPolynomial (ULift.{u} ℤ)))) from terminal.hom_ext _ _]
  exact IsPullback.of_hasPullback _ _

/-- The first inclusion of the punctured line is the base change of
`AlgebraicGeometry.projectiveLinePuncturedChart` along the projection of `𝔸¹_S` to `𝔸¹_ℤ`. -/
theorem isPullback_puncturedChartOver (S : Scheme.{u}) :
    IsPullback (puncturedChartOver S)
      (pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ))))))
      (pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (projectiveLinePuncturedChart (ULift.{u} ℤ)) :=
  isPullback_of_fst_snd S _ _ (puncturedChartOver_fst S) (puncturedChartOver_snd S)

/-- The second inclusion of the punctured line is the base change of the inverse overlap
coordinate along the projection of `𝔸¹_S` to `𝔸¹_ℤ`. -/
theorem isPullback_puncturedYChartOver (S : Scheme.{u}) :
    IsPullback (puncturedYChartOver S)
      (pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (LaurentPolynomial (ULift.{u} ℤ))))))
      (pullback.snd (terminal.from S)
        (terminal.from (AlgebraicGeometry.Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (Spec.map (CommRingCat.ofHom
        (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom)) :=
  isPullback_of_fst_snd S _ _ (puncturedYChartOver_fst S) (puncturedYChartOver_snd S)

/-- The first inclusion of the punctured line is an open immersion. -/
instance isOpenImmersion_puncturedChartOver (S : Scheme.{u}) :
    IsOpenImmersion (puncturedChartOver S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_puncturedChartOver S).flip inferInstance

/-- The second inclusion of the punctured line is an open immersion. -/
instance isOpenImmersion_puncturedYChartOver (S : Scheme.{u}) :
    IsOpenImmersion (puncturedYChartOver S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_puncturedYChartOver S).flip
    (isOpenImmersion_specMap_projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ))

/-! ### The punctured line is nonempty and integral -/

/-- The section of the relative punctured line through the point `T = 1`, obtained by base
changing `Stacks.Chow.laurentEvalOne`. It witnesses that the punctured line is nonempty as soon
as `S` is. -/
def puncturedLineOneSection (S : Scheme.{u}) : S ⟶ puncturedLineOver S :=
  pullback.lift (𝟙 S)
    (terminal.from S ≫ specULiftZIsTerminal.from (⊤_ Scheme.{u}) ≫ Spec.map laurentEvalOne)
    (terminal.hom_ext _ _)

/-- The relative punctured line over a nonempty scheme is nonempty. -/
instance nonempty_puncturedLineOver (S : Scheme.{u}) [Nonempty S] :
    Nonempty (puncturedLineOver S) :=
  ⟨(puncturedLineOneSection S).base ‹Nonempty S›.some⟩

/-- The relative punctured line over an integral scheme is integral: it is a nonempty open
subscheme of the integral affine line `𝔸¹_S`. -/
instance isIntegral_puncturedLineOver (S : Scheme.{u}) [IsIntegral S] [Nonempty S] :
    IsIntegral (puncturedLineOver S) :=
  isIntegral_of_isOpenImmersion (puncturedChartOver S)

/-! ### The two pullbacks of the affine coordinate are inverse to each other -/

/-- The inverse overlap coordinate sends the coordinate of `ℤ[T]` to `T⁻¹`. -/
private theorem projectiveLineOverlapInverseCoordinate_X (k : Type u) [CommRing k] :
    (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom)
        (Polynomial.X : Polynomial k) =
      LaurentPolynomial.T (-1) :=
  Polynomial.aeval_X _

/-- The coordinate of `ℤ[T]` pulls back to `T` along the inclusion of the punctured line. -/
private theorem appTop_puncturedChart_inv_X :
    (projectiveLinePuncturedChart (ULift.{u} ℤ)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
        (LaurentPolynomial.T 1) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  exact congrArg _ Polynomial.toLaurent_X

/-- The coordinate of `ℤ[T]` pulls back to `T⁻¹` along the inverse overlap coordinate. -/
private theorem appTop_specMap_overlapInverse_inv_X :
    (Spec.map (CommRingCat.ofHom
          (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
        (LaurentPolynomial.T (-1)) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  exact congrArg _ (projectiveLineOverlapInverseCoordinate_X (ULift.{u} ℤ))

/-- The pullback of the affine coordinate along the first inclusion of the punctured line is
the Laurent coordinate `T`. -/
theorem puncturedChartOver_appTop_affineCoordinate (S : Scheme.{u}) :
    (puncturedChartOver S).appTop (affineCoordinate S) =
      (pullback.snd (terminal.from S)
          (terminal.from (AlgebraicGeometry.Spec
            (.of (LaurentPolynomial (ULift.{u} ℤ)))))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
          (LaurentPolynomial.T 1)) := by
  rw [affineCoordinate_eq, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    puncturedChartOver_snd, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    appTop_puncturedChart_inv_X]

/-- The pullback of the affine coordinate along the second inclusion of the punctured line is
the inverse Laurent coordinate `T⁻¹`. -/
theorem puncturedYChartOver_appTop_affineCoordinate (S : Scheme.{u}) :
    (puncturedYChartOver S).appTop (affineCoordinate S) =
      (pullback.snd (terminal.from S)
          (terminal.from (AlgebraicGeometry.Spec
            (.of (LaurentPolynomial (ULift.{u} ℤ)))))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
          (LaurentPolynomial.T (-1))) := by
  rw [affineCoordinate_eq, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    puncturedYChartOver_snd, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    appTop_specMap_overlapInverse_inv_X]

/-- **The gluing relation of the affine coordinate.** The two pullbacks of the affine coordinate
of `𝔸¹_S` to the relative punctured line are inverse to each other. -/
theorem puncturedChartOver_appTop_affineCoordinate_mul (S : Scheme.{u}) :
    (puncturedChartOver S).appTop (affineCoordinate S) *
      (puncturedYChartOver S).appTop (affineCoordinate S) = 1 := by
  rw [puncturedChartOver_appTop_affineCoordinate, puncturedYChartOver_appTop_affineCoordinate,
    ← map_mul, ← map_mul, ← LaurentPolynomial.T_add, add_neg_cancel,
    LaurentPolynomial.T_zero, map_one, map_one]

/-! ### The packaged comparison -/

/-- **The gluing relation of `ℙ¹_S`.** There is an integral scheme `W` — the relative punctured
line — with two open immersions into `𝔸¹_S` which agree after composing with the two affine
charts of `ℙ¹_S`, and along which the two pullbacks of the affine coordinate are inverse to each
other. -/
theorem exists_puncturedComparison (S : Scheme.{u}) [IsIntegral S] [Nonempty S] :
    ∃ (W : Scheme.{u}) (α β : W ⟶ affineLineOver S),
      Nonempty W ∧ AlgebraicGeometry.IsIntegral W ∧ IsOpenImmersion α ∧ IsOpenImmersion β ∧
      α ≫ affineChart S = β ≫ affineYChart S ∧
      α.appTop (affineCoordinate S) * β.appTop (affineCoordinate S) = 1 :=
  ⟨puncturedLineOver S, puncturedChartOver S, puncturedYChartOver S, inferInstance,
    inferInstance, inferInstance, inferInstance, puncturedChartOver_comp_affineChart S,
    puncturedChartOver_appTop_affineCoordinate_mul S⟩

end Stacks.Chow

end
