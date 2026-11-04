module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonoidal

/-!
# Lifting a graded duality to the twisted Karoubi envelope

Let `C` be a graded monoidal category and let `Y` be a left dual of `X` in `C`
(Categories, Definition 0FFP; Mathlib's `ExactPairing X Y`), with unit
`η : 𝟙 ⟶ X ⊗ Y` homogeneous of degree `d` and counit `ε : Y ⊗ X ⟶ 𝟙` homogeneous of degree `-d`.
Then in the twisted Karoubi envelope of `C` the triple `(Y, 𝟙, d - m)` is a left dual of
`(X, 𝟙, m)`, with the same unit and counit: the degrees are exactly those of morphisms
`(𝟙, 𝟙, 0) ⟶ (X ⊗ Y, 𝟙, d)` and `(Y ⊗ X, 𝟙, d) ⟶ (𝟙, 𝟙, 0)`, and the two triangle identities are
those of `C`, the idempotents being identities.

For the graded category of correspondences between smooth projective schemes over a field, with
`X = Y` equidimensional of dimension `d` and `η = ε = [Δ]`, this is how Stacks 0FGI produces the
duality `h(X)(d)` of `h(X)` in `M_k`.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.exactPairingOfObj`: the left dual
  `(Y, 𝟙, d - m)` of `(X, 𝟙, m)`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.exactPairingOfObj_coevaluation_val` and
  `CategoryTheory.GradedCategory.TwistedKaroubi.exactPairingOfObj_evaluation_val`: the unit and
  the counit are those of `C`.

## References

* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C]

/-- The unit of a graded duality, as a morphism `(𝟙, 𝟙, 0) ⟶ (X, 𝟙, m) ⊗ (Y, 𝟙, d - m)` of
triples. -/
def coevaluationOfObj {X Y : C} (η : 𝟙_ C ⟶ X ⊗ Y) {d : ℤ} (hη : η ∈ grade (R := R) _ _ d)
    (m : ℤ) :
    𝟙_ (TwistedKaroubi R C) ⟶
      ({ ofObj (R := R) X with twist := m } : TwistedKaroubi R C) ⊗
        { ofObj (R := R) Y with twist := d - m } :=
  Hom.mk η ⟨grade_cast hη (by simp), Category.id_comp _, by
    change η ≫ (𝟙 X ⊗ₘ 𝟙 Y) = η
    rw [MonoidalCategory.id_tensorHom_id, Category.comp_id]⟩

/-- The counit of a graded duality, as a morphism `(Y, 𝟙, d - m) ⊗ (X, 𝟙, m) ⟶ (𝟙, 𝟙, 0)` of
triples. -/
def evaluationOfObj {X Y : C} (ε : Y ⊗ X ⟶ 𝟙_ C) {d : ℤ} (hε : ε ∈ grade (R := R) _ _ (-d))
    (m : ℤ) :
    ({ ofObj (R := R) Y with twist := d - m } : TwistedKaroubi R C) ⊗
        { ofObj (R := R) X with twist := m } ⟶ 𝟙_ (TwistedKaroubi R C) :=
  Hom.mk ε ⟨grade_cast hε (by simp), by
    change (𝟙 Y ⊗ₘ 𝟙 X) ≫ ε = ε
    rw [MonoidalCategory.id_tensorHom_id, Category.id_comp], Category.comp_id _⟩

/-- **A graded duality lifts to the twisted Karoubi envelope.** If `Y` is a left dual of `X` in
`C`, with unit homogeneous of degree `d` and counit homogeneous of degree `-d`, then
`(Y, 𝟙, d - m)` is a left dual of `(X, 𝟙, m)`, with the same unit and counit. -/
@[instance_reducible]
def exactPairingOfObj (X Y : C) [ExactPairing X Y] {d : ℤ}
    (hη : η_ X Y ∈ grade (R := R) _ _ d) (hε : ε_ X Y ∈ grade (R := R) _ _ (-d)) (m : ℤ) :
    ExactPairing ({ ofObj (R := R) X with twist := m } : TwistedKaroubi R C)
      { ofObj (R := R) Y with twist := d - m } where
  coevaluation' := coevaluationOfObj (η_ X Y) hη m
  evaluation' := evaluationOfObj (ε_ X Y) hε m
  coevaluation_evaluation' := by
    apply hom_ext
    change (𝟙 Y ⊗ₘ η_ X Y) ≫ ((𝟙 Y ⊗ₘ 𝟙 X ⊗ₘ 𝟙 Y) ≫ (α_ Y X Y).inv) ≫ (ε_ X Y ⊗ₘ 𝟙 Y) =
      ((𝟙 Y ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ Y).hom) ≫ 𝟙 Y ≫ (λ_ Y).inv
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_whiskerRight, Category.id_comp]
    exact ExactPairing.coevaluation_evaluation X Y
  evaluation_coevaluation' := by
    apply hom_ext
    change (η_ X Y ⊗ₘ 𝟙 X) ≫ (((𝟙 X ⊗ₘ 𝟙 Y) ⊗ₘ 𝟙 X) ≫ (α_ X Y X).hom) ≫ (𝟙 X ⊗ₘ ε_ X Y) =
      ((𝟙 (𝟙_ C) ⊗ₘ 𝟙 X) ≫ (λ_ X).hom) ≫ 𝟙 X ≫ (ρ_ X).inv
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_whiskerRight, Category.id_comp]
    exact ExactPairing.evaluation_coevaluation X Y

/-- The unit of the lifted duality `exactPairingOfObj X Y hη hε m` has underlying morphism the
unit `η_ X Y` of `C`. -/
@[simp]
theorem exactPairingOfObj_coevaluation_val (X Y : C) [ExactPairing X Y] {d : ℤ}
    (hη : η_ X Y ∈ grade (R := R) _ _ d) (hε : ε_ X Y ∈ grade (R := R) _ _ (-d)) (m : ℤ) :
    (@ExactPairing.coevaluation _ _ _ _ _ (exactPairingOfObj X Y hη hε m)).val = η_ X Y :=
  rfl

/-- The counit of the lifted duality `exactPairingOfObj X Y hη hε m` has underlying morphism the
counit `ε_ X Y` of `C`. -/
@[simp]
theorem exactPairingOfObj_evaluation_val (X Y : C) [ExactPairing X Y] {d : ℤ}
    (hη : η_ X Y ∈ grade (R := R) _ _ d) (hε : ε_ X Y ∈ grade (R := R) _ _ (-d)) (m : ℤ) :
    (@ExactPairing.evaluation _ _ _ _ _ (exactPairingOfObj X Y hη hε m)).val = ε_ X Y :=
  rfl

end CategoryTheory.GradedCategory.TwistedKaroubi

end
