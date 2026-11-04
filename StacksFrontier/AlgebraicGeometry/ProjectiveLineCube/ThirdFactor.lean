module

public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCube.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic

/-!
# A product of three factors as a product of two

For schemes `S` and `X`, the product `S × X × X × X` over `Spec ℤ` is the product over `Spec ℤ` of
`S × X × X`, by the projection forgetting the third factor, and of `X`, by the third projection.
This is the form in which a family over `S × X × X` with fibres in the third factor `X` is
described, for instance the double covers of `S × ℙ¹ × ℙ¹` cut out in `S × ℙ¹ × ℙ¹ × ℙ¹` by a
binary quadratic form in the coordinates of the third factor.

## Main definitions

* `AlgebraicGeometry.cubeProduct.firstTwo S X`: the product `S × X × X`.
* `AlgebraicGeometry.cubeProduct.forgetThird`: the projection `S × X × X × X ⟶ S × X × X`.

## Main results

* `AlgebraicGeometry.cubeProduct.isPullback_forgetThird_proj`: `S × X × X × X` is the product of
  `S × X × X` and `X`, with projections `forgetThird` and `proj S X 2`.
* `AlgebraicGeometry.cubeProduct.forgetThird_comp_firstTwoProj`: the first two projections
  factor through `forgetThird`.
* `AlgebraicGeometry.projectiveLineCube.coordinate_eval_top`: the pencil `𝓗ᵢ` with its two
  coordinate sections is the pair attached by [Stacks, Tag 01NE] to the `i`-th projection to
  `ℙ¹_ℤ`.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace cubeProduct

variable (S X : Scheme.{u})

/-- The product `S × X × X` of schemes over `Spec ℤ`. -/
abbrev firstTwo : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (pullback (terminal.from X) (terminal.from X)))

/-- The two projections of `S × X × X` to `X`. -/
def firstTwoProj : Fin 2 → (firstTwo S X ⟶ X) :=
  ![pullback.snd _ _ ≫ pullback.fst _ _, pullback.snd _ _ ≫ pullback.snd _ _]

/-- The projection `S × X × X × X ⟶ S × X × X` forgetting the third factor. -/
def forgetThird : cubeProduct S X ⟶ firstTwo S X :=
  pullback.lift (toBase S X) (pullback.lift (proj S X 0) (proj S X 1) (terminal.hom_ext _ _))
    (terminal.hom_ext _ _)

/-- `forgetThird` is a morphism over `S`. -/
@[reassoc (attr := simp)]
theorem forgetThird_fst : forgetThird S X ≫ pullback.fst _ _ = toBase S X :=
  pullback.lift_fst _ _ _

/-- The composite of `forgetThird` with the projection `S × X × X ⟶ X` to the first `X` factor is
`proj S X 0`. -/
@[reassoc (attr := simp)]
theorem forgetThird_snd_fst :
    forgetThird S X ≫ pullback.snd _ _ ≫ pullback.fst _ _ = proj S X 0 := by
  rw [forgetThird, pullback.lift_snd_assoc, pullback.lift_fst]

/-- The composite of `forgetThird` with the projection `S × X × X ⟶ X` to the second `X` factor
is `proj S X 1`. -/
@[reassoc (attr := simp)]
theorem forgetThird_snd_snd :
    forgetThird S X ≫ pullback.snd _ _ ≫ pullback.snd _ _ = proj S X 1 := by
  rw [forgetThird, pullback.lift_snd_assoc, pullback.lift_snd]

/-- **The first two projections factor through `forgetThird`.** -/
@[reassoc]
theorem forgetThird_comp_firstTwoProj (i : Fin 2) :
    forgetThird S X ≫ firstTwoProj S X i = proj S X i.castSucc := by
  fin_cases i
  · exact forgetThird_snd_fst S X
  · exact forgetThird_snd_snd S X

/-- The `i`-th projection, for `i = 0, 1`, factors through `forgetThird`. -/
theorem exists_forgetThird_comp_eq_proj (i : Fin 3) (hi : i ≠ 2) :
    ∃ k : firstTwo S X ⟶ X, forgetThird S X ≫ k = proj S X i := by
  fin_cases i
  · exact ⟨firstTwoProj S X 0, forgetThird_comp_firstTwoProj S X 0⟩
  · exact ⟨firstTwoProj S X 1, forgetThird_comp_firstTwoProj S X 1⟩
  · exact absurd rfl hi

/-- **`S × X × X × X` is the product of `S × X × X` and the third factor `X`.** -/
theorem isPullback_forgetThird_proj :
    IsPullback (forgetThird S X) (proj S X 2) (terminal.from (firstTwo S X)) (terminal.from X) := by
  refine IsPullback.of_isLimit' ⟨terminal.hom_ext _ _⟩ (PullbackCone.IsLimit.mk _
      (fun s => lift (s.fst ≫ pullback.fst _ _)
        ![s.fst ≫ pullback.snd _ _ ≫ pullback.fst _ _, s.fst ≫ pullback.snd _ _ ≫ pullback.snd _ _,
          s.snd])
      (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_))
  · refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · change (lift _ _ ≫ forgetThird S X) ≫ _ = _
      rw [Category.assoc, forgetThird_fst, lift_toBase]
    all_goals
      change (lift _ _ ≫ forgetThird S X) ≫ _ ≫ _ = _
      rw [Category.assoc]
    · rw [forgetThird_snd_fst]
      exact lift_proj _ _ 0
    · rw [forgetThird_snd_snd]
      exact lift_proj _ _ 1
  · exact lift_proj _ _ 2
  · change m ≫ forgetThird S X = s.fst at h₁
    change m ≫ proj S X 2 = s.snd at h₂
    refine hom_ext ?_ fun i => ?_
    · rw [lift_toBase, ← h₁, Category.assoc, forgetThird_fst]
    · rw [lift_proj]
      fin_cases i
      · simp [← h₁]
      · simp [← h₁]
      · exact h₂

end cubeProduct

namespace projectiveLineCube

variable (S : Scheme.{u})

/-- The pencil `𝓗ᵢ = prᵢ^*𝒪(1)` is the module of the pair attached to the `i`-th projection by
[Stacks, Tag 01NE]. -/
theorem lineBundle_eq_tautological_bundle (i : Fin 3) :
    lineBundle S i =
      (Stacks.ProjectiveSpaceModuli.tautological (cubeProduct.proj S _ i)).bundle :=
  rfl

/-- **The coordinate sections of the pencil `𝓗ᵢ` are the sections of the pair attached to the
`i`-th projection by [Stacks, Tag 01NE]**: `prᵢ^*Tₐ` is the pullback of the homogeneous coordinate
`Tₐ`. -/
theorem coordinate_eval_top (i : Fin 3) (a : Fin 2) :
    (coordinate S i a).eval (Opposite.op ⊤) =
      (Stacks.ProjectiveSpaceModuli.tautological (cubeProduct.proj S _ i)).coord a :=
  (Stacks.SheafOfModules.modulePullbackSection_eval_top _ _ _).trans
    (Stacks.NonvanishingPullback.pullbackGlobalSections_eq_pullbackGlobalSection _ _ _).symm

end projectiveLineCube

end AlgebraicGeometry
