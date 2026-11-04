module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Retract
import StacksCore.Tactic.StacksAttribute

/-!
# Duals in a monoidal category

Mathlib coverage for Stacks chapter 4 (Categories) section 43.

## Main definitions

* `CategoryTheory.ExactPairing.map`: a monoidal functor carries a left dual to a left dual.
  Mathlib has only the reflection `CategoryTheory.ExactPairing.ofFaithful` along a faithful
  monoidal functor, not this direct image.
* `Stacks.ExactPairing.ofJointlyFaithful`: candidate coevaluation and evaluation data is an
  exact pairing as soon as a *jointly* faithful family of monoidal functors carries it to one.
  Mathlib's `CategoryTheory.ExactPairing.ofFaithful` needs a single faithful functor, which the
  restriction to one slice of a site is not.
* `CategoryTheory.ExactPairing.retractOfCoevaluationFactors`: if the coevaluation of an exact
  pairing factors through `K ⊗ Y` along a morphism `K ⟶ X`, then `X` is a retract of `K`.
* `CategoryTheory.tensorRightIhomAdjunction`: in a braided monoidal closed category, tensoring
  on the right is left adjoint to the internal hom.
* `CategoryTheory.rightDualIsoIhomUnit`: in a braided monoidal closed category a left dual of
  `X` is canonically isomorphic to the internal hom `Hom(X, 𝟙)`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- **A monoidal functor carries a left dual to a left dual.** If `Y` is a left dual of `X`,
then `F.obj Y` is a left dual of `F.obj X`: the coevaluation and the evaluation are the images
of those of `X, Y` conjugated by the unit and tensor structure maps of `F`. -/
@[instance_reducible]
def ExactPairing.map (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' := ε F ≫ F.map (η_ X Y) ≫ δ F X Y
  evaluation' := μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  evaluation_coevaluation' := by
    have key : ∀ {Z : D} (h : F.obj (X ⊗ 𝟙_ C) ⟶ Z),
        F.map (η_ X Y ▷ X) ≫ F.map (α_ X Y X).hom ≫ F.map (X ◁ ε_ X Y) ≫ h =
          F.map (λ_ X).hom ≫ F.map (ρ_ X).inv ≫ h := fun h => by
      simp only [← Functor.map_comp_assoc, ExactPairing.evaluation_coevaluation]
    rw [Functor.Monoidal.map_associator']
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.Monoidal.whiskerLeft_δ_μ_assoc,
      μ_natural_left_assoc, δ_natural_right_assoc]
    rw [key, ← Functor.OplaxMonoidal.oplax_right_unitality,
      ← Functor.LaxMonoidal.left_unitality_assoc]
  coevaluation_evaluation' := by
    have key : ∀ {Z : D} (h : F.obj (𝟙_ C ⊗ Y) ⟶ Z),
        F.map (Y ◁ η_ X Y) ≫ F.map (α_ Y X Y).inv ≫ F.map (ε_ X Y ▷ Y) ≫ h =
          F.map (ρ_ Y).hom ≫ F.map (λ_ Y).inv ≫ h := fun h => by
      simp only [← Functor.map_comp_assoc, ExactPairing.coevaluation_evaluation]
    rw [Functor.Monoidal.map_associator_inv']
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.Monoidal.whiskerLeft_δ_μ_assoc,
      μ_natural_right_assoc, δ_natural_left_assoc]
    rw [key, ← Functor.OplaxMonoidal.oplax_left_unitality,
      ← Functor.LaxMonoidal.right_unitality_assoc]

/-- The coevaluation of the image pairing is the image of the coevaluation. -/
theorem ExactPairing.map_coevaluation (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    letI := ExactPairing.map F X Y
    η_ (F.obj X) (F.obj Y) = ε F ≫ F.map (η_ X Y) ≫ δ F X Y :=
  rfl

/-- The evaluation of the image pairing is the image of the evaluation. -/
theorem ExactPairing.map_evaluation (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    letI := ExactPairing.map F X Y
    ε_ (F.obj X) (F.obj Y) = μ F Y X ≫ F.map (ε_ X Y) ≫ η F :=
  rfl

/-- **A factorization of the coevaluation exhibits the object as a retract.** Let `Y` be a left
dual of `X`, and suppose the coevaluation `η : 𝟙 ⟶ X ⊗ Y` factors as `coev ≫ f ▷ Y` through
`K ⊗ Y` along a morphism `f : K ⟶ X`. Then `X` is a retract of `K`, the section being

`X ≅ 𝟙 ⊗ X --coev ▷ X--> (K ⊗ Y) ⊗ X ≅ K ⊗ (Y ⊗ X) --K ◁ ε--> K ⊗ 𝟙 ≅ K`,

and the retraction being `f` itself. Only one of the two triangle identities is used, namely
`CategoryTheory.ExactPairing.evaluation_coevaluation`.

This is the formal content of the direct-summand step in the proof of Stacks 0FPD: there the
coevaluation of a pairing in `D(O_X)` is, after restricting to a small enough open, a finite sum
`Σ fᵢ ⊗ gᵢ`, hence factors through `K ⊗ Y` for any subobject `K` of `X` containing the `fᵢ`, and
the source then reads off that `X` is a direct summand of `K`. Nothing about complexes, sheaves
or finiteness enters here — the passage from a factorization to a retract is monoidal yoga. -/
def ExactPairing.retractOfCoevaluationFactors {X Y K : C} [ExactPairing X Y] (f : K ⟶ X)
    (coev : 𝟙_ C ⟶ K ⊗ Y) (hcoev : coev ≫ f ▷ Y = η_ X Y) : Retract X K where
  i := (λ_ X).inv ≫ coev ▷ X ≫ (α_ K Y X).hom ≫ K ◁ ε_ X Y ≫ (ρ_ K).hom
  r := f
  retract := by
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      ← MonoidalCategory.rightUnitor_naturality,
      MonoidalCategory.whisker_exchange_assoc,
      ← MonoidalCategory.associator_naturality_left_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, hcoev,
      ExactPairing.evaluation_coevaluation_assoc]
    simp

/-- The retraction of `CategoryTheory.ExactPairing.retractOfCoevaluationFactors` is the given
morphism `f`, so the retract it produces is a retract *along* `f` and not along some other
morphism of the same type. -/
@[simp]
theorem ExactPairing.retractOfCoevaluationFactors_r {X Y K : C} [ExactPairing X Y] (f : K ⟶ X)
    (coev : 𝟙_ C ⟶ K ⊗ Y) (hcoev : coev ≫ f ▷ Y = η_ X Y) :
    (ExactPairing.retractOfCoevaluationFactors f coev hcoev).r = f :=
  rfl

section Closed

variable [BraidedCategory C] [MonoidalClosed C]

/-- **Tensoring on the right is left adjoint to the internal hom** in a braided monoidal closed
category: `ihom.adjunction` states this for tensoring on the left, and the two
differ by the braiding. -/
def tensorRightIhomAdjunction (X : C) : tensorRight X ⊣ ihom X :=
  (ihom.adjunction X).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight X)

/-- **A left dual is the internal hom into the unit.** In a braided monoidal closed category, a
left dual `Y` of `X` — Mathlib's `ExactPairing X Y` — is canonically isomorphic to
`Hom(X, 𝟙)`.

Both `- ⊗ Y` and `Hom(X, -)` are right adjoint to `- ⊗ X`: the first because of the pairing, the
second because the category is closed and braided. So they are isomorphic by uniqueness of right
adjoints, and the isomorphism at the unit is the statement. No rigidity is assumed: only the one
object `X` is required to have a dual. -/
def rightDualIsoIhomUnit (X Y : C) [ExactPairing X Y] :
    Y ≅ (ihom X).obj (𝟙_ C) :=
  (λ_ Y).symm ≪≫
    ((tensorRightAdjunction X Y).rightAdjointUniq (tensorRightIhomAdjunction X)).app (𝟙_ C)

end Closed

end CategoryTheory

namespace Stacks

universe v₁ v₃ u₁ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- **An exact pairing can be checked along a jointly faithful family of monoidal functors.**
Given candidate data `coeval : 𝟙 ⟶ X ⊗ Y` and `eval : Y ⊗ X ⟶ 𝟙`, suppose each member of a
family `F i` of monoidal functors carries it to the coevaluation and the evaluation of an exact
pairing of `F i X` with `F i Y`. If the family is jointly faithful — two morphisms agreeing
after every `F i` are equal — then the two triangle identities hold for `coeval` and `eval`
themselves.

This is `CategoryTheory.ExactPairing.ofFaithful` with one faithful functor replaced by a
jointly faithful family, which is what a *local* verification looks like: no single restriction
functor to a slice of a site is faithful, but the restrictions to the members of a covering
family are jointly faithful
(`Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`). -/
@[instance_reducible]
def ExactPairing.ofJointlyFaithful {ι : Type u₃} {D : ι → Type u₄} [∀ i, Category.{v₃} (D i)]
    [∀ i, MonoidalCategory (D i)] (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (hF : ∀ {A B : C} (f g : A ⟶ B), (∀ i, (F i).map f = (F i).map g) → f = g)
    {X Y : C} (eval : Y ⊗ X ⟶ 𝟙_ C) (coeval : 𝟙_ C ⟶ X ⊗ Y)
    [∀ i, ExactPairing ((F i).obj X) ((F i).obj Y)]
    (map_eval : ∀ i, (F i).map eval = δ (F i) Y X ≫ ε_ ((F i).obj X) ((F i).obj Y) ≫ ε (F i))
    (map_coeval : ∀ i, (F i).map coeval =
      η (F i) ≫ η_ ((F i).obj X) ((F i).obj Y) ≫ μ (F i) X Y) :
    ExactPairing X Y where
  evaluation' := eval
  coevaluation' := coeval
  evaluation_coevaluation' := hF _ _ fun i => by
    simp [map_eval i, map_coeval i, Functor.Monoidal.map_whiskerLeft,
      Functor.Monoidal.map_whiskerRight]
  coevaluation_evaluation' := hF _ _ fun i => by
    simp [map_eval i, map_coeval i, Functor.Monoidal.map_whiskerLeft,
      Functor.Monoidal.map_whiskerRight]

end Stacks

/- Stacks 0FFS: if `Yᵢ` is a left dual of `Xᵢ` then `Y₂ ⊗ Y₁` is a left dual of `X₁ ⊗ X₂`. Mathlib
states this in the opposite index convention, `[ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂]` giving
`ExactPairing (X₁ ⊗ X₂) (Y₂ ⊗ Y₁)`; substituting `X₁ := Y₂`, `Y₁ := X₂`, `X₂ := Y₁`, `Y₂ := X₁`
recovers the Stacks statement verbatim. -/
add_to_stacks 0FFS CategoryTheory.ExactPairing.tensor
