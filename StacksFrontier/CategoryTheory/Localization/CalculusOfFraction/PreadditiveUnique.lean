module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Preadditive.Opposite
import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of the preadditive structure on a localization (Stacks 05QD)

Let `C` be a preadditive category and `W` a left or right multiplicative system on `C`.
Mathlib constructs a preadditive structure on the localization making the localization
functor additive when `W` has a left calculus of fractions
(`CategoryTheory.Localization.preadditive`, `CategoryTheory.Localization.functor_additive`).
This file adds the right case, by duality through `L.op`, and the uniqueness of such a
structure in both cases, and states Stacks 05QD in full as
`CategoryTheory.Localization.existsUnique_preadditive_functor_additive`.

## References

* [Stacks Project, Tag 05QD](https://stacks.math.columbia.edu/tag/05QD)
-/

@[expose] public section

namespace CategoryTheory.Localization

open Opposite

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

/-- Two preadditive structures on a category are equal if they have the same addition
of morphisms. -/
private lemma preadditive_eq_of_add_eq {P₁ P₂ : Preadditive D}
    (h : ∀ ⦃X Y : D⦄ (f g : X ⟶ Y), (letI := P₁; f + g) = (letI := P₂; f + g)) : P₁ = P₂ := by
  rcases P₁ with ⟨G₁, _, _⟩
  rcases P₂ with ⟨G₂, _, _⟩
  congr
  funext X Y
  exact AddCommGroup.ext (funext₂ fun f g ↦ h f g)

/-- If `L : C ⥤ D` is a localization functor for a morphism property `W` with a left calculus
of fractions on a preadditive category `C`, then there is at most one preadditive structure
on `D` making `L` additive. -/
@[stacks 05QD "Uniqueness, for a left multiplicative system."]
lemma preadditive_eq_of_hasLeftCalculusOfFractions [W.HasLeftCalculusOfFractions]
    (P₁ P₂ : Preadditive D) (h₁ : @Functor.Additive _ _ _ _ _ P₁ L)
    (h₂ : @Functor.Additive _ _ _ _ _ P₂ L) : P₁ = P₂ := by
  have key : @Functor.Additive D D _ _ P₁ P₂ (𝟭 D) :=
    (@functor_additive_iff _ _ _ _ _ L W _ _ D _ P₂ P₁ h₁ (𝟭 D)).2 ⟨h₂.map_add⟩
  exact preadditive_eq_of_add_eq fun _ _ _ _ ↦ key.map_add

/-- The preadditive structure on `D`, when `L : C ⥤ D` is a localization functor,
`C` is preadditive and there is a right calculus of fractions. It is obtained by
applying `Localization.preadditive` to `L.op`. -/
@[instance_reducible]
noncomputable def preadditive' [W.HasRightCalculusOfFractions] : Preadditive D :=
  letI := preadditive L.op W.op
  { homGroup X Y := Equiv.addCommGroup (opEquiv (op Y) (op X)).symm
    add_comp _ _ _ f f' g :=
      Quiver.Hom.op_inj (CategoryTheory.Preadditive.comp_add _ _ _ g.op f.op f'.op)
    comp_add _ _ _ f g g' :=
      Quiver.Hom.op_inj (CategoryTheory.Preadditive.add_comp _ _ _ g.op g'.op f.op) }

/-- The localization functor `L` is additive for the preadditive structure
`Localization.preadditive'` given by a right calculus of fractions. -/
@[stacks 05QD "Existence, for a right multiplicative system."]
lemma functor_additive' [W.HasRightCalculusOfFractions] :
    letI := preadditive' L W
    L.Additive :=
  letI := preadditive L.op W.op
  haveI := functor_additive L.op W.op
  @Functor.Additive.mk _ _ _ _ _ (preadditive' L W) L fun {_ _ f g} ↦
    Quiver.Hom.op_inj (L.op.map_add (f := f.op) (g := g.op))

/-- If `L : C ⥤ D` is a localization functor for a morphism property `W` with a right calculus
of fractions on a preadditive category `C`, then there is at most one preadditive structure
on `D` making `L` additive. -/
@[stacks 05QD "Uniqueness, for a right multiplicative system."]
lemma preadditive_eq_of_hasRightCalculusOfFractions [W.HasRightCalculusOfFractions]
    (P₁ P₂ : Preadditive D) (h₁ : @Functor.Additive _ _ _ _ _ P₁ L)
    (h₂ : @Functor.Additive _ _ _ _ _ P₂ L) : P₁ = P₂ := by
  let Q₁ : Preadditive Dᵒᵖ := @instPreadditiveOpposite D _ P₁
  let Q₂ : Preadditive Dᵒᵖ := @instPreadditiveOpposite D _ P₂
  have h : Q₁ = Q₂ := preadditive_eq_of_hasLeftCalculusOfFractions L.op W.op Q₁ Q₂
    (@Functor.op_additive C _ _ D _ P₁ L h₁) (@Functor.op_additive C _ _ D _ P₂ L h₂)
  refine preadditive_eq_of_add_eq fun X Y f g ↦ ?_
  exact congrArg (fun P : Preadditive Dᵒᵖ ↦ (letI := P; f.op + g.op).unop) h

/-- Let `C` be a preadditive category and `W` a morphism property on `C` with a left or a right
calculus of fractions (i.e. a left or right multiplicative system), and let `L : C ⥤ D` be a
localization functor for `W` (e.g. `W.Q : C ⥤ W.Localization`). Then there is a unique
preadditive structure on `D` such that `L` is additive. -/
@[stacks 05QD]
theorem existsUnique_preadditive_functor_additive
    (hW : W.HasLeftCalculusOfFractions ∨ W.HasRightCalculusOfFractions) :
    ∃! P : Preadditive D, @Functor.Additive _ _ _ _ _ P L := by
  rcases hW with hW | hW
  · exact ⟨preadditive L W, functor_additive L W, fun P hP ↦
      preadditive_eq_of_hasLeftCalculusOfFractions L W P _ hP (functor_additive L W)⟩
  · exact ⟨preadditive' L W, functor_additive' L W, fun P hP ↦
      preadditive_eq_of_hasRightCalculusOfFractions L W P _ hP (functor_additive' L W)⟩

end CategoryTheory.Localization
