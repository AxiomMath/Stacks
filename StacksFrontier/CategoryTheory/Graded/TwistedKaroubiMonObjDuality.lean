module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonObj
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTate
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiUnitTwistTrace
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Self-dual monoids among the untwisted triples

Let `C` be a graded braided monoidal category and `X` an object of `C` which is its own left dual,
with unit `η : 𝟙 ⟶ X ⊗ X` of degree `d` and counit `ε : X ⊗ X ⟶ 𝟙` of degree `-d`. Then
`(X, 𝟙, 0) ⊗ T(d)`, with `T(d) = (𝟙, 𝟙, d)` the twisted unit, is a left dual of `(X, 𝟙, 0)` in
the twisted Karoubi envelope, with unit `η` and counit `ε` (up to the unitor `X ⊗ 𝟙 ≅ X`). If
moreover `X` is a monoid and `ε = μ ≫ t` for a morphism `t : X ⟶ 𝟙` of degree `-d`, then the
counit of triples is the multiplication followed by `t`:

  `ε = α ≫ (X ◁ β_{T(d), X}) ≫ α⁻¹ ≫ (μ ▷ T(d)) ≫ t'`,

where `t' = unitTwistTrace d t : (X, 𝟙, 0) ⊗ T(d) ⟶ 𝟙` is `t` (up to the unitor). This is the
shape in which Poincaré duality for a realization of Chow motives is proved (Stacks 0FH1, 0FHK):
for a smooth projective scheme `X` of dimension `d` the counit of the duality of Stacks 0FGI is
`[X] ∘ [Γ_Δ]`.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.exactPairingOfObjTensorTwist`: the duality
  between `(X, 𝟙, 0)` and `(X, 𝟙, 0) ⊗ T(d)`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.evaluation_eq_mul_comp`: the counit is the
  multiplication followed by `t`, for any monoid structure and duality with these underlying
  morphisms (`exactPairingOfObjTensorTwist_evaluation_val`).
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory MonObj Category

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C]

attribute [-instance] TwistedKaroubi.monoidalCategoryStruct

section Duality

variable (X : C) [ExactPairing X X] {d : ℤ}

/-- The unit `η ≫ (X ◁ ρ⁻¹) : 𝟙 ⟶ X ⊗ (X ⊗ 𝟙)` of the duality between `(X, 𝟙, 0)` and
`(X, 𝟙, 0) ⊗ T(d)`. -/
def coevaluationOfObjTensorTwist (hη : η_ X X ∈ grade (R := R) _ _ d) :
    𝟙_ (TwistedKaroubi R C) ⟶ ofObj (R := R) X ⊗ (ofObj (R := R) X ⊗ tateTriple R C d) :=
  have hm : η_ X X ≫ X ◁ (ρ_ X).inv ∈ grade (R := R) _ _ d := by
    have h := comp_mem (R := R) (IsGradedMonoidal.tensorHom_mem (R := R) (id_mem X)
      (IsGradedMonoidal.rightUnitor_inv_mem (R := R) X)) hη
    rwa [id_tensorHom, add_zero, zero_add] at h
  Hom.mk (η_ X X ≫ X ◁ (ρ_ X).inv) ⟨grade_cast hm (by simp),
    Category.id_comp _, by
      have h : (η_ X X ≫ X ◁ (ρ_ X).inv) ≫ (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ 𝟙 (𝟙_ C))) =
          η_ X X ≫ X ◁ (ρ_ X).inv := by
        rw [id_tensorHom_id, id_tensorHom_id, Category.comp_id]
      exact h⟩

/-- The counit `(ρ ▷ X) ≫ ε : (X ⊗ 𝟙) ⊗ X ⟶ 𝟙` of the duality between `(X, 𝟙, 0)` and
`(X, 𝟙, 0) ⊗ T(d)`. -/
def evaluationOfObjTensorTwist (hε : ε_ X X ∈ grade (R := R) _ _ (-d)) :
    (ofObj (R := R) X ⊗ tateTriple R C d) ⊗ ofObj (R := R) X ⟶ 𝟙_ (TwistedKaroubi R C) :=
  have hm : (ρ_ X).hom ▷ X ≫ ε_ X X ∈ grade (R := R) _ _ (-d) := by
    have h := comp_mem (R := R) hε (IsGradedMonoidal.tensorHom_mem (R := R)
      (IsGradedMonoidal.rightUnitor_hom_mem (R := R) X) (id_mem X))
    rwa [tensorHom_id, add_zero, add_zero] at h
  Hom.mk ((ρ_ X).hom ▷ X ≫ ε_ X X) ⟨grade_cast hm (by simp), by
      have h : ((𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ⊗ₘ 𝟙 X) ≫ ((ρ_ X).hom ▷ X ≫ ε_ X X) =
          (ρ_ X).hom ▷ X ≫ ε_ X X := by
        rw [id_tensorHom_id, id_tensorHom_id, Category.id_comp]
      exact h, Category.comp_id _⟩

/-- The underlying morphism of `coevaluationOfObjTensorTwist X hη` is `η ≫ (X ◁ ρ⁻¹)`. -/
theorem coevaluationOfObjTensorTwist_val (hη : η_ X X ∈ grade (R := R) _ _ d) :
    (coevaluationOfObjTensorTwist (R := R) X hη).val = η_ X X ≫ X ◁ (ρ_ X).inv :=
  rfl

/-- The underlying morphism of `evaluationOfObjTensorTwist X hε` is `(ρ ▷ X) ≫ ε`. -/
theorem evaluationOfObjTensorTwist_val (hε : ε_ X X ∈ grade (R := R) _ _ (-d)) :
    (evaluationOfObjTensorTwist (R := R) X hε).val = (ρ_ X).hom ▷ X ≫ ε_ X X :=
  rfl

/-- **A self-duality of `X` of degree `d` makes `(X, 𝟙, 0) ⊗ T(d)` a left dual of `(X, 𝟙, 0)`**,
with unit `η ≫ (X ◁ ρ⁻¹)` and counit `(ρ ▷ X) ≫ ε`. -/
@[instance_reducible]
def exactPairingOfObjTensorTwist (hη : η_ X X ∈ grade (R := R) _ _ d)
    (hε : ε_ X X ∈ grade (R := R) _ _ (-d)) :
    ExactPairing (ofObj (R := R) X) (ofObj (R := R) X ⊗ tateTriple R C d) where
  coevaluation' := coevaluationOfObjTensorTwist X hη
  evaluation' := evaluationOfObjTensorTwist X hε
  coevaluation_evaluation' := by
    let : ExactPairing X (X ⊗ 𝟙_ C) := exactPairingCongrRight (ρ_ X)
    have h₀ := ExactPairing.coevaluation_evaluation X (X ⊗ 𝟙_ C)
    have h : ((𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ⊗ₘ (η_ X X ≫ X ◁ (ρ_ X).inv)) ≫
        (((𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ⊗ₘ (𝟙 X ⊗ₘ (𝟙 X ⊗ₘ 𝟙 (𝟙_ C)))) ≫ (α_ _ _ _).inv) ≫
          (((ρ_ X).hom ▷ X ≫ ε_ X X) ⊗ₘ (𝟙 X ⊗ₘ 𝟙 (𝟙_ C))) =
        (((𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (X ⊗ 𝟙_ C)).hom) ≫
          ((𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (X ⊗ 𝟙_ C)).inv) := by
      simp only [id_tensorHom, tensorHom_id, Category.id_comp, MonoidalCategory.id_whiskerRight]
      exact h₀
    exact hom_ext h
  evaluation_coevaluation' := by
    let : ExactPairing X (X ⊗ 𝟙_ C) := exactPairingCongrRight (ρ_ X)
    have h₀ := ExactPairing.evaluation_coevaluation X (X ⊗ 𝟙_ C)
    have h : ((η_ X X ≫ X ◁ (ρ_ X).inv) ⊗ₘ 𝟙 X) ≫
        (((𝟙 X ⊗ₘ (𝟙 X ⊗ₘ 𝟙 (𝟙_ C))) ⊗ₘ 𝟙 X) ≫ (α_ _ _ _).hom) ≫
          (𝟙 X ⊗ₘ ((ρ_ X).hom ▷ X ≫ ε_ X X)) =
        ((𝟙 (𝟙_ C) ⊗ₘ 𝟙 X) ≫ (λ_ X).hom) ≫ (𝟙 X ≫ (ρ_ X).inv) := by
      simp only [id_tensorHom, tensorHom_id, Category.id_comp, MonoidalCategory.id_whiskerRight]
      exact h₀
    exact hom_ext h

end Duality

variable [BraidedCategory C] [IsGradedBraided R C]

/-- **The counit of a self-dual monoid is its multiplication followed by `t`.** Let `(X, 𝟙, 0)`
carry a monoid structure with underlying multiplication `μ`, and a left dual
`(X, 𝟙, 0) ⊗ T(d)` with underlying counit `(ρ ▷ X) ≫ ε`. If `ε = μ ≫ t` for some `t : X ⟶ 𝟙` of
degree `-d`, then the counit is `α ≫ (X ◁ β) ≫ α⁻¹ ≫ (μ ▷ T(d)) ≫ t'`, with `t'` the morphism of
triples given by `t`. The monoid and the duality are arbitrary instances, described through
their underlying morphisms. -/
theorem evaluation_eq_mul_comp {X : C} {d : ℤ} [MonObj (ofObj (R := R) X)]
    [ExactPairing (ofObj (R := R) X) (ofObj (R := R) X ⊗ tateTriple R C d)]
    (μX : X ⊗ X ⟶ X) (ε : X ⊗ X ⟶ 𝟙_ C)
    (hev : (ε_ (ofObj (R := R) X) (ofObj (R := R) X ⊗ tateTriple R C d)).val =
      (ρ_ X).hom ▷ X ≫ ε)
    (hμ : (μ[ofObj (R := R) X]).val = μX)
    (t : X ⟶ 𝟙_ C) (ht : t ∈ grade (R := R) _ _ (-d)) (hεt : ε = μX ≫ t) :
    ε_ (ofObj (R := R) X) (ofObj (R := R) X ⊗ tateTriple R C d) =
      (α_ (ofObj (R := R) X) (tateTriple R C d) (ofObj (R := R) X)).hom ≫
        ofObj (R := R) X ◁ (β_ (tateTriple R C d) (ofObj (R := R) X)).hom ≫
          (α_ (ofObj (R := R) X) (ofObj (R := R) X) (tateTriple R C d)).inv ≫
            μ ▷ tateTriple R C d ≫ unitTwistTrace d t ht := by
  have h : (ρ_ X).hom ▷ X ≫ ε =
      (((𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ⊗ₘ 𝟙 X) ≫ (α_ X (𝟙_ C) X).hom) ≫
        (𝟙 X ⊗ₘ ((𝟙 (𝟙_ C) ⊗ₘ 𝟙 X) ≫ (β_ (𝟙_ C) X).hom)) ≫
          ((𝟙 X ⊗ₘ (𝟙 X ⊗ₘ 𝟙 (𝟙_ C))) ≫ (α_ X X (𝟙_ C)).inv) ≫
            (μX ⊗ₘ 𝟙 (𝟙_ C)) ≫ ((ρ_ X).hom ≫ t) := by
    simp only [id_tensorHom, tensorHom_id, Category.id_comp, MonoidalCategory.id_whiskerRight,
      braiding_tensorUnit_left, hεt]
    rw [rightUnitor_naturality_assoc]
    monoidal
  apply hom_ext
  rw [hev, h, ← hμ]
  rfl

omit [BraidedCategory C] [IsGradedBraided R C] in
/-- The counit of `exactPairingOfObjTensorTwist`, as a morphism of `C`. -/
theorem exactPairingOfObjTensorTwist_evaluation_val (X : C) [ExactPairing X X] {d : ℤ}
    (hη : η_ X X ∈ grade (R := R) _ _ d) (hε : ε_ X X ∈ grade (R := R) _ _ (-d)) :
    (@ExactPairing.evaluation _ _ _ _ _ (exactPairingOfObjTensorTwist (R := R) X hη hε)).val =
      (ρ_ X).hom ▷ X ≫ ε_ X X :=
  rfl

end CategoryTheory.GradedCategory.TwistedKaroubi

end
