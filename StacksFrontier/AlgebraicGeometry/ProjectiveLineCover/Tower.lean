module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineReduction
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCover.Surjective

/-!
# The finite surjective cover of `ℙⁿ_S` by the `n`-fold power of `ℙ¹_S`

The morphism `((x₁ : y₁), …, (xₙ : yₙ)) ↦ (F₀ : … : Fₙ)`, where
`∏ (xᵢ T + yᵢ) = F₀ Tⁿ + … + Fₙ`, from the `n`-fold fibre power of the projective line over `S`
onto `ℙⁿ_S` is finite and surjective. It is built by induction on `n` from the multiplication
`ℙ¹ × ℙⁿ ⟶ ℙⁿ⁺¹` of `Stacks.ProjectiveLineCover.multiplication`: the cover at stage `n + 1` is the
projective line over the cover at stage `n`, followed by the base change of the multiplication to
`S`. Both are base changes of finite surjective morphisms. At stage `0` it is the inverse of the
isomorphism `ℙ⁰_S ⟶ S`.

## Main results

* `Stacks.ProjectiveLineCover.hasProjectiveLineTowerCover`: the cover is finite, surjective and
  lies over `S`, which is `Stacks.EtaleCohomology.HasProjectiveLineTowerCover`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.ProjectiveLineCover

/-- The product over the terminal scheme, base changed along a morphism of the second factor. -/
theorem isPullback_map_right {A B C : Scheme.{u}} (f : A ⟶ B) :
    IsPullback (pullback.map (terminal.from C) (terminal.from A) (terminal.from C)
        (terminal.from B) (𝟙 C) f (𝟙 _) (by simp) (terminal.hom_ext _ _))
      (pullback.snd _ _) (pullback.snd _ _) f := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, Category.comp_id, terminal.comp_from]
  exact IsPullback.of_hasPullback _ _

/-- The product over the terminal scheme, base changed along a morphism of the first factor. -/
theorem isPullback_map_left {A B C : Scheme.{u}} (f : A ⟶ B) :
    IsPullback (pullback.map (terminal.from A) (terminal.from C) (terminal.from B)
        (terminal.from C) f (𝟙 C) (𝟙 _) (terminal.hom_ext _ _) (by simp))
      (pullback.fst _ _) (pullback.fst _ _) f := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (terminal.from B) (terminal.from C)).flip
  rw [pullback.lift_snd, Category.comp_id, terminal.comp_from]
  exact (IsPullback.of_hasPullback _ _).flip

/-- Projective `n`-space over `S` written out as a fibre product with the integral model;
`AlgebraicGeometry.ProjectiveSpace n S` unfolds to it. -/
abbrev PS (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))

/-- `ℙ⁰_S ⟶ S` is an isomorphism. -/
theorem isIso_projectiveSpace_zero_over (S : Scheme.{u}) :
    IsIso (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 0))) := by
  have := Stacks.DeRham.isIso_terminalFrom_projectiveSpaceAtUniverse_of_zero.{u}
  infer_instance

variable (S : Scheme.{u}) (n : ℕ)

/-- The comparison `ℙ¹_{ℙⁿ_S} ⟶ ℙ¹ × ℙⁿ` over the integers. -/
def toProd : PS.{u} 1 (PS.{u} n S) ⟶ Prod.{u} n :=
  pullback.map (terminal.from (PS.{u} n S)) (terminal.from (projectiveSpaceAtUniverse.{u} 1))
    (terminal.from (projectiveSpaceAtUniverse.{u} n))
    (terminal.from (projectiveSpaceAtUniverse.{u} 1))
    (pullback.snd _ _) (𝟙 _) (𝟙 _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- The multiplication `ℙ¹_{ℙⁿ_S} ⟶ ℙⁿ⁺¹_S` over `S`. -/
def mulOver : PS.{u} 1 (PS.{u} n S) ⟶ PS.{u} (n + 1) S :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (toProd S n ≫ multiplication.{u} n)
    (terminal.hom_ext _ _)

/-- The composite of `mulOver S n` with the projection `ℙⁿ⁺¹_S ⟶ S` is the projection
`ℙ¹_{ℙⁿ_S} ⟶ S`. -/
theorem mulOver_fst : mulOver S n ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The composite of `mulOver S n` with the projection to `ℙⁿ⁺¹` over the integers is
`toProd S n` followed by the multiplication over the integers. -/
theorem mulOver_snd : mulOver S n ≫ pullback.snd _ _ = toProd S n ≫ multiplication.{u} n :=
  pullback.lift_snd _ _ _

/-- `ℙ¹_{ℙⁿ_S} = S ×_ℤ (ℙ¹ × ℙⁿ)`. -/
theorem isPullback_toProd_outer :
    IsPullback (toProd S n) (pullback.fst _ _ ≫ pullback.fst _ _)
      (terminal.from (Prod.{u} n)) (terminal.from S) := by
  have h1 := isPullback_map_left (C := projectiveSpaceAtUniverse.{u} 1)
    (pullback.snd (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)))
  have h2 := (IsPullback.of_hasPullback (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse.{u} n)))
  have h3 := h1.flip.paste_horiz h2
  rw [show pullback.fst (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from (projectiveSpaceAtUniverse.{u} 1)) ≫
        terminal.from (projectiveSpaceAtUniverse.{u} n) =
      terminal.from (Prod.{u} n) from terminal.hom_ext _ _] at h3
  exact h3.flip

/-- **The multiplication over `S` is the base change of the multiplication over the integers.** -/
theorem isPullback_mulOver :
    IsPullback (toProd S n) (mulOver S n) (multiplication.{u} n) (pullback.snd _ _) := by
  refine IsPullback.of_bot ?_ (mulOver_snd S n).symm
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} (n + 1)))).flip
  rw [mulOver_fst, terminal.comp_from]
  exact isPullback_toProd_outer S n

/-- The multiplication `mulOver S n : ℙ¹_{ℙⁿ_S} ⟶ ℙⁿ⁺¹_S` is finite. -/
instance : IsFinite (mulOver S n) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_mulOver S n) inferInstance

/-- The multiplication `mulOver S n : ℙ¹_{ℙⁿ_S} ⟶ ℙⁿ⁺¹_S` is surjective. -/
instance : Surjective (mulOver S n) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_mulOver S n) inferInstance

/-- The projective line over a morphism. -/
def lineMap {T T' : Scheme.{u}} (f : T ⟶ T') : PS.{u} 1 T ⟶ PS.{u} 1 T' :=
  pullback.map (terminal.from T) (terminal.from (projectiveSpaceAtUniverse.{u} 1))
    (terminal.from T') (terminal.from (projectiveSpaceAtUniverse.{u} 1)) f (𝟙 _) (𝟙 _)
    (terminal.hom_ext _ _) (by simp)

/-- The map `lineMap f : ℙ¹_T ⟶ ℙ¹_{T'}` lies over `f`. -/
@[reassoc]
theorem lineMap_fst {T T' : Scheme.{u}} (f : T ⟶ T') :
    lineMap f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f :=
  pullback.lift_fst _ _ _

/-- The projective line `lineMap f` over a finite morphism `f` is finite. -/
instance {T T' : Scheme.{u}} (f : T ⟶ T') [IsFinite f] : IsFinite (lineMap f) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_map_left f).flip inferInstance

/-- The projective line `lineMap f` over a surjective morphism `f` is surjective. -/
instance {T T' : Scheme.{u}} (f : T ⟶ T') [Surjective f] : Surjective (lineMap f) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_map_left f).flip inferInstance

/-- A cover of `ℙⁿ_S` by the tower together with its three properties. -/
theorem exists_towerCover : ∃ c : projectiveLineTower S n ⟶ PS.{u} n S,
    IsFinite c ∧ Surjective c ∧ c ≫ pullback.fst _ _ = projectiveLineTowerHom S n := by
  induction n with
  | zero =>
      show ∃ c : S ⟶ PS.{u} 0 S, IsFinite c ∧ Surjective c ∧ c ≫ pullback.fst _ _ = 𝟙 S
      have := isIso_projectiveSpace_zero_over S
      exact ⟨inv (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 0))),
        inferInstance, inferInstance, IsIso.inv_hom_id _⟩
  | succ n ih =>
      obtain ⟨c, hfin, hsurj, hc⟩ := ih
      show ∃ c : PS.{u} 1 (projectiveLineTower S n) ⟶ PS.{u} (n + 1) S,
        IsFinite c ∧ Surjective c ∧ c ≫ pullback.fst _ _ = pullback.fst _ _ ≫
          projectiveLineTowerHom S n
      refine ⟨lineMap c ≫ mulOver S n, inferInstance, inferInstance, ?_⟩
      rw [Category.assoc, mulOver_fst, lineMap_fst_assoc, hc]

/-- **The finite surjective cover of `ℙⁿ_S` by the `n`-fold power of `ℙ¹_S`**, the display in the
last paragraph of [Stacks, Tag 0A4F]: `((x₁ : y₁), …, (xₙ : yₙ)) ↦ (F₀ : … : Fₙ)` where
`∏ (xᵢ T + yᵢ) = F₀ Tⁿ + … + Fₙ` is finite, surjective, and over `S`. -/
theorem hasProjectiveLineTowerCover : Stacks.EtaleCohomology.HasProjectiveLineTowerCover.{u} :=
  fun S n => exists_towerCover S n

end Stacks.ProjectiveLineCover
