module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineReduction
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.Defs

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjOfPolynomialOneVariable
public import StacksFrontier.AlgebraicGeometry.Limits.BinaryFormMultiplicationSurjective
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveLineTower

/-!
# The tower of projective lines covers projective space

The `n`-fold fibre power `(ℙ¹_S)ⁿ`, realised as the tower
`AlgebraicGeometry.projectiveLineTower S n`, maps **surjectively** onto `ℙⁿ_S` over `S`. This is
the display in the last paragraph of the proof of [Stacks, Tag 0A4F]:
`((x₁ : y₁), …, (xₙ : yₙ)) ↦ (F₀ : ⋯ : Fₙ)` with `∏ᵢ (xᵢ t + yᵢ) = ∑ⱼ Fⱼ tⁿ⁻ʲ`,
a point of `(ℙ¹)ⁿ` being sent to the product of the corresponding linear forms.

The map is built one factor at a time: the `(n+1)`-st stage of the tower is `ℙ¹` over the `n`-th,
and the step multiplies a binary form of degree `n` by a linear form, which is the base change to
`S` of `AlgebraicGeometry.ProjectiveSpace.binaryFormMul n : ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ ⟶ ℙⁿ⁺¹_ℤ`.
Surjectivity of that integral multiplication is
`AlgebraicGeometry.ProjectiveSpace.surjective_binaryFormMul`, and surjectivity is stable under base
change and composition. The tower starts at `ℙ⁰_S ≅ S`, because `ℙ⁰_ℤ = Proj ℤ[T] ≅ Spec ℤ`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpace.mulOver`: the multiplication of binary forms over a base `S`,
  `ℙ¹_{ℙⁿ_S} ⟶ ℙⁿ⁺¹_S`.

## Main results

* `AlgebraicGeometry.ProjectiveSpace.isIso_terminal_from_zero`: `ℙ⁰_ℤ` is `Spec ℤ`.
* `AlgebraicGeometry.ProjectiveSpace.surjective_mulOver`: the multiplication over `S` is
  surjective.
* `AlgebraicGeometry.exists_surjective_projectiveLineTower`: **the tower of projective lines maps
  surjectively onto `ℙⁿ_S` over `S`.**

## References

* [Stacks Project, Tag 0A4F](https://stacks.math.columbia.edu/tag/0A4F)
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Stacks.SectionsToProjectiveSpace

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **`ℙ⁰_ℤ` is `Spec ℤ`**: the structure morphism of the integral model of projective `0`-space
to the terminal scheme is an isomorphism, since `Proj ℤ[T] ≅ Spec ℤ`. -/
theorem isIso_terminal_from_zero : IsIso (terminal.from (ProjectiveSpaceZ.{u} 0)) :=
  isIso_of_isTerminal
    (specULiftZIsTerminal.ofIso (oneVariableProjIsoSpec (ULift.{u} ℤ)).symm)
    terminalIsTerminal _

/-- **`ℙ⁰_S ⟶ S` is an isomorphism**, being the base change of `ℙ⁰_ℤ ⟶ Spec ℤ`. -/
instance isIso_over_zero (S : Scheme.{u}) : IsIso (ProjectiveSpace 0 S ↘ S) := by
  have := isIso_terminal_from_zero.{u}
  rw [over_hom]
  exact pullback_fst_iso_of_right_iso _ _

variable (n : ℕ) (S : Scheme.{u})

/-- The projection `ℙ¹_{ℙⁿ_S} ⟶ ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ`, forgetting `S`. -/
def mulOverLift : ProjectiveSpace 1 (ProjectiveSpace n S) ⟶ mulSource.{u} n :=
  pullback.lift (f := terminal.from (Proj (coordGrading.{u} n)))
    (g := terminal.from (Proj (coordGrading.{u} 1)))
    (pullback.fst (terminal.from (ProjectiveSpace n S)) (terminal.from (ProjectiveSpaceZ.{u} 1)) ≫
      toProjectiveSpaceZ n S)
    (pullback.snd (terminal.from (ProjectiveSpace n S)) (terminal.from (ProjectiveSpaceZ.{u} 1)))
    (terminal.hom_ext _ _)

/-- **The multiplication of binary forms over `S`**, `ℙ¹_{ℙⁿ_S} ⟶ ℙⁿ⁺¹_S`: the base change of
`AlgebraicGeometry.ProjectiveSpace.binaryFormMul n` along `S ⟶ Spec ℤ`. -/
def mulOver : ProjectiveSpace 1 (ProjectiveSpace n S) ⟶ ProjectiveSpace (n + 1) S :=
  pullback.lift (f := terminal.from S) (g := terminal.from (ProjectiveSpaceZ.{u} (n + 1)))
    (pullback.fst (terminal.from (ProjectiveSpace n S)) (terminal.from (ProjectiveSpaceZ.{u} 1)) ≫
      (ProjectiveSpace n S ↘ S))
    (mulOverLift n S ≫ binaryFormMul n) (terminal.hom_ext _ _)

/-- The multiplication over `S` is a morphism over `ℙⁿ_S ⟶ S`. -/
theorem mulOver_over : mulOver n S ≫ (ProjectiveSpace (n + 1) S ↘ S) =
    pullback.fst (terminal.from (ProjectiveSpace n S)) (terminal.from (ProjectiveSpaceZ.{u} 1)) ≫
      (ProjectiveSpace n S ↘ S) :=
  pullback.lift_fst _ _ _

/-- The multiplication over `S` lies over the integral multiplication. -/
theorem mulOver_toProjectiveSpaceZ : mulOver n S ≫ toProjectiveSpaceZ (n + 1) S =
    mulOverLift n S ≫ binaryFormMul n :=
  pullback.lift_snd _ _ _

/-- `ℙ¹_{ℙⁿ_S}` is the base change of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ` along `S ⟶ Spec ℤ`. -/
theorem isPullback_mulOverLift : IsPullback (mulOverLift n S)
    (pullback.fst (terminal.from (ProjectiveSpace n S)) (terminal.from (ProjectiveSpaceZ.{u} 1)) ≫
      (ProjectiveSpace n S ↘ S)) (mulFst n ≫ terminal.from (ProjectiveSpaceZ.{u} n))
      (terminal.from S) := by
  have s : IsPullback (mulOverLift n S ≫ mulSnd n)
      (pullback.fst (terminal.from (ProjectiveSpace n S)) (terminal.from (ProjectiveSpaceZ.{u} 1)))
      (terminal.from (ProjectiveSpaceZ.{u} 1))
      (toProjectiveSpaceZ n S ≫ terminal.from (ProjectiveSpaceZ.{u} n)) := by
    rw [show mulOverLift n S ≫ mulSnd n = pullback.snd (terminal.from (ProjectiveSpace n S))
        (terminal.from (ProjectiveSpaceZ.{u} 1)) from pullback.lift_snd _ _ _,
      terminal.comp_from]
    exact (IsPullback.of_hasPullback _ _).flip
  have hTop : IsPullback (mulOverLift n S)
      (pullback.fst (terminal.from (ProjectiveSpace n S)) (terminal.from (ProjectiveSpaceZ.{u} 1)))
      (mulFst n) (toProjectiveSpaceZ n S) :=
    IsPullback.of_right s (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
  exact hTop.paste_vert
    (IsPullback.of_hasPullback (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} n))).flip

/-- **The multiplication over `S` is the base change of the integral multiplication.** -/
theorem isPullback_mulOver : IsPullback (mulOverLift n S) (mulOver n S) (binaryFormMul n)
    (toProjectiveSpaceZ (n + 1) S) := by
  have aux : ∀ (v : ProjectiveSpace 1 (ProjectiveSpace n S) ⟶ S)
      (g : mulSource.{u} n ⟶ ⊤_ Scheme.{u}),
      v = pullback.fst (terminal.from (ProjectiveSpace n S))
        (terminal.from (ProjectiveSpaceZ.{u} 1)) ≫ (ProjectiveSpace n S ↘ S) →
      g = mulFst n ≫ terminal.from (ProjectiveSpaceZ.{u} n) →
      IsPullback (mulOverLift n S) v g (terminal.from S) := by
    rintro v g rfl rfl
    exact isPullback_mulOverLift n S
  have s : IsPullback (mulOverLift n S) (mulOver n S ≫ (ProjectiveSpace (n + 1) S ↘ S))
      (binaryFormMul n ≫ terminal.from (ProjectiveSpaceZ.{u} (n + 1))) (terminal.from S) :=
    aux _ _ (mulOver_over n S) (terminal.hom_ext _ _)
  exact IsPullback.of_bot s (mulOver_toProjectiveSpaceZ n S).symm
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (ProjectiveSpaceZ.{u} (n + 1)))).flip

/-- **The multiplication of binary forms over `S` is surjective**, being the base change of the
integral multiplication (`AlgebraicGeometry.ProjectiveSpace.surjective_binaryFormMul`). -/
theorem surjective_mulOver : Surjective (mulOver.{u} n S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
    (isPullback_mulOver n S) (surjective_binaryFormMul n)

end ProjectiveSpace

open ProjectiveSpace in
/-- **The tower of projective lines maps surjectively onto projective space.** For every scheme
`S` and every `n` there is a surjective morphism over `S` from the `n`-fold fibre power of `ℙ¹_S`,
realised as `AlgebraicGeometry.projectiveLineTower S n`, onto `ℙⁿ_S`. It is the map of the last
paragraph of the proof of [Stacks, Tag 0A4F], sending `n` linear forms to their product: the
`(n+1)`-st step is the base change of the multiplication `ℙⁿ × ℙ¹ ⟶ ℙⁿ⁺¹` of binary forms. -/
theorem exists_surjective_projectiveLineTower (S : Scheme.{u}) (n : ℕ) :
    ∃ c : projectiveLineTower S n ⟶ ProjectiveSpace n S,
      Surjective c ∧ c ≫ (ProjectiveSpace n S ↘ S) = projectiveLineTowerHom S n := by
  induction n with
  | zero =>
      refine ⟨(inv (ProjectiveSpace 0 S ↘ S) : S ⟶ ProjectiveSpace 0 S),
        inferInstanceAs (Surjective (inv (ProjectiveSpace 0 S ↘ S))), ?_⟩
      exact IsIso.inv_hom_id (ProjectiveSpace 0 S ↘ S)
  | succ n ih =>
      obtain ⟨c, hc, hcS⟩ := ih
      have : MorphismProperty.IsStableUnderComposition @Surjective.{u} :=
        MorphismProperty.IsMultiplicative.toIsStableUnderComposition
      let c₁ : ProjectiveSpace 1 (projectiveLineTower S n) ⟶
          ProjectiveSpace 1 (ProjectiveSpace n S) :=
        pullback.map (terminal.from (projectiveLineTower S n))
          (terminal.from (ProjectiveSpaceZ.{u} 1)) (terminal.from (ProjectiveSpace n S))
          (terminal.from (ProjectiveSpaceZ.{u} 1)) c (𝟙 _) (𝟙 _) (terminal.hom_ext _ _)
          (by simp)
      have hc₁ : Surjective c₁ :=
        MorphismProperty.pullback_map (P := @Surjective.{u}) hc
          (inferInstanceAs (Surjective (𝟙 _))) (terminal.hom_ext _ _) (by simp)
      have hm := surjective_mulOver n S
      refine ⟨c₁ ≫ mulOver n S, inferInstanceAs (Surjective (c₁ ≫ mulOver n S)), ?_⟩
      show (c₁ ≫ mulOver n S) ≫ _ =
        (ProjectiveSpace 1 (projectiveLineTower S n) ↘ projectiveLineTower S n) ≫
          projectiveLineTowerHom S n
      rw [Category.assoc, mulOver_over, ← hcS, over_hom]
      exact pullback.lift_fst_assoc _ _ _ _

end AlgebraicGeometry

end
