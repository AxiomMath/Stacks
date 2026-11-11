module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Localization.Opposite
public import StacksCore.CategoryTheory.Abelian.Opposite
public import StacksCore.Tactic.StacksAttribute

/-!
# The localization of an additive category is additive

Let `C` be an additive category (a preadditive category with finite biproducts) and let `W` be
a left or right multiplicative system, i.e. a morphism property with a left or a right calculus
of fractions. For any localization functor `L : C ⥤ D` for `W`, the category `D` carries a
preadditive structure for which `L` is additive, and `D` then has a zero object and finite
biproducts: `D` is an additive category.

Mathlib provides the preadditive structure in the left case (`Localization.preadditive`). The
right case is deduced from it by passing to opposite categories.

## Main results

* `Stacks.Localization.hasFiniteBiproducts_of_additive`
* `Stacks.Localization.preadditiveOfHasRightCalculusOfFractions`
* `Stacks.Localization.functor_additive_of_hasRightCalculusOfFractions`
* `Stacks.Localization.exists_preadditive_additive_hasFiniteBiproducts`
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace Stacks.Localization

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W]

include W in
/-- If `C` is preadditive with finite biproducts and `L : C ⥤ D` is an additive localization
functor between preadditive categories, then `D` has finite biproducts. -/
lemma hasFiniteBiproducts_of_additive [Preadditive C] [HasFiniteBiproducts C] [Preadditive D]
    [L.Additive] : HasFiniteBiproducts D := by
  have := CategoryTheory.Localization.essSurj L W
  have : HasZeroObject D := L.hasZeroObject_of_additive
  have := hasBinaryBiproducts_of_finite_biproducts C
  have := preservesBinaryBiproducts_of_preservesBiproducts L
  have : HasBinaryBiproducts D := ⟨fun X Y =>
    hasBinaryBiproduct_of_iso (L.objObjPreimageIso X) (L.objObjPreimageIso Y)⟩
  have := hasFiniteProducts_of_has_binary_and_terminal (C := D)
  exact HasFiniteBiproducts.of_hasFiniteProducts

section Right

variable [Preadditive C] [W.HasRightCalculusOfFractions]

/-- The preadditive structure on the target of a localization functor `L : C ⥤ D` for a
morphism property `W` with a right calculus of fractions on a preadditive category `C`. It is
the preadditive structure `Localization.preadditive L.op W.op` on `Dᵒᵖ`, transported to `D`. -/
@[instance_reducible]
noncomputable def preadditiveOfHasRightCalculusOfFractions : Preadditive D :=
  letI : Preadditive Dᵒᵖ := CategoryTheory.Localization.preadditive L.op W.op
  CategoryTheory.Preadditive.fromOpposite

/-- A localization functor `L : C ⥤ D` for a morphism property with a right calculus of
fractions on a preadditive category is additive for the preadditive structure
`preadditiveOfHasRightCalculusOfFractions L W` on `D`. -/
lemma functor_additive_of_hasRightCalculusOfFractions :
    letI := preadditiveOfHasRightCalculusOfFractions L W
    L.Additive := by
  let hD : Preadditive Dᵒᵖ := CategoryTheory.Localization.preadditive L.op W.op
  have hL := CategoryTheory.Localization.functor_additive L.op W.op
  let := preadditiveOfHasRightCalculusOfFractions L W
  exact ⟨fun {X Y f g} => Quiver.Hom.op_inj
    (@Functor.Additive.map_add _ _ _ _ _ hD L.op hL _ _ f.op g.op)⟩

end Right

/-- Let `C` be an additive category (a preadditive category with finite biproducts) and let `W`
be a left or right multiplicative system (a morphism property with a left or a right calculus of
fractions). Then the target `D` of any localization functor `L : C ⥤ D` for `W` (for instance
`W.Q : C ⥤ W.Localization`) is an additive category and `L` is additive: there is a preadditive
structure on `D` for which `L` is additive and `D` has a zero object and finite biproducts. -/
@[stacks 05QE]
theorem exists_preadditive_additive_hasFiniteBiproducts [Preadditive C] [HasFiniteBiproducts C]
    (hW : W.HasLeftCalculusOfFractions ∨ W.HasRightCalculusOfFractions) :
    ∃ P : Preadditive D, letI := P; L.Additive ∧ HasZeroObject D ∧ HasFiniteBiproducts D := by
  obtain hW | hW := hW
  · let := CategoryTheory.Localization.preadditive L W
    have := CategoryTheory.Localization.functor_additive L W
    exact ⟨_, this, L.hasZeroObject_of_additive, hasFiniteBiproducts_of_additive L W⟩
  · let := preadditiveOfHasRightCalculusOfFractions L W
    have := functor_additive_of_hasRightCalculusOfFractions L W
    exact ⟨_, this, L.hasZeroObject_of_additive, hasFiniteBiproducts_of_additive L W⟩

end Stacks.Localization
