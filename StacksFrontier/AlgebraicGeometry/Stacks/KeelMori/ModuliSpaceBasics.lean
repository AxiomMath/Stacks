module

public import StacksFrontier.AlgebraicGeometry.Stacks.CategoricalModuliSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TrivialBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients

/-!
# Elementary properties of categorical moduli spaces

Three consequences of the definitions of Stacks 0DUG used in the proof of the Keel–Mori theorem
(Stacks 0DUT):

* a uniform categorical moduli space is a categorical moduli space;
* the base change of a uniform categorical moduli space along a flat morphism is again a uniform
  categorical moduli space;
* two categorical moduli spaces of the same category fibred in groupoids are isomorphic, by an
  isomorphism compatible with the two 1-morphisms.

## Main results

* `AlgebraicGeometry.Stack.isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace`
* `AlgebraicGeometry.Stack.isUniformCategoricalModuliSpace_fst`
* `AlgebraicGeometry.Stack.exists_iso_of_isCategoricalModuliSpace`

## References

* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The 1-morphism attached to the identity of a presheaf is the identity. -/
theorem associatedMap_id_eq (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (associatedMap B S hS (𝟙 F)).1 = 𝟙 (fibredCategory B S hS F) :=
  hom_eq_of_hom₂ B S hS (nonempty_twoIso_associatedMap_id B S hS F).some.hom

/-- **A uniform categorical moduli space is a categorical moduli space**: it is its own base
change along the identity, which is flat. -/
theorem isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace {Y : AlgebraicSpaces B S hS}
    {f : 𝒳 ⟶ fibredCategory B S hS Y.obj}
    (hf : IsUniformCategoricalModuliSpace B S hS Y f) : IsCategoricalModuliSpace B S hS Y f := by
  have key := hf Y (𝟙 Y) (Space.isFlat_id B S hS Y.property)
  change ∀ P : Bicategory.TwoCommSq (associatedMap B S hS (𝟙 Y.obj)).1 f,
    Bicategory.IsTwoFibreProduct P → IsCategoricalModuliSpace B S hS Y P.fst at key
  rw [associatedMap_id_eq] at key
  exact key (Bicategory.trivialBaseChangeSquare f).swap
    (Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_trivialBaseChangeSquare f
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f (𝟙 _))))

/-- **The base change of a uniform categorical moduli space along a flat morphism is a uniform
categorical moduli space.** A further flat base change of the base change is, by pasting, a flat
base change of the original one. -/
theorem isUniformCategoricalModuliSpace_fst {Y Y' : AlgebraicSpaces B S hS}
    {f : 𝒳 ⟶ fibredCategory B S hS Y.obj}
    (hf : IsUniformCategoricalModuliSpace B S hS Y f) (a : Y' ⟶ Y)
    (ha : Space.IsFlat B S hS a.hom) (P : Bicategory.TwoCommSq (associatedMap B S hS a.hom).1 f)
    (hP : Bicategory.IsTwoFibreProduct P) :
    IsUniformCategoricalModuliSpace B S hS Y' P.fst := by
  intro Y'' b hb Q hQ
  have key := hf Y'' (b ≫ a) (Space.isFlat_comp B S hS Y''.property Y'.property Y.property
    b.hom a.hom hb ha)
  change ∀ P : Bicategory.TwoCommSq (associatedMap B S hS (b.hom ≫ a.hom)).1 f,
    Bicategory.IsTwoFibreProduct P → IsCategoricalModuliSpace B S hS Y'' P.fst at key
  rw [associatedMap_comp] at key
  exact key (P.pasteFst Q) (Bicategory.isTwoFibreProduct_pasteFst P hP Q hQ)

/-- **Two categorical moduli spaces of the same category fibred in groupoids are isomorphic**, by
an isomorphism under which the two 1-morphisms correspond. -/
theorem exists_iso_of_isCategoricalModuliSpace {Y Y' : AlgebraicSpaces B S hS}
    {f : 𝒳 ⟶ fibredCategory B S hS Y.obj} {f' : 𝒳 ⟶ fibredCategory B S hS Y'.obj}
    (hf : IsCategoricalModuliSpace B S hS Y f) (hf' : IsCategoricalModuliSpace B S hS Y' f') :
    ∃ e : Y ≅ Y', f ≫ (associatedMap B S hS e.hom.hom).1 = f' := by
  obtain ⟨h, ⟨η⟩, -⟩ := hf Y' f'
  obtain ⟨h', ⟨η'⟩, -⟩ := hf' Y f
  have hid : ∀ {Z : AlgebraicSpaces B S hS} {z : 𝒳 ⟶ fibredCategory B S hS Z.obj},
      IsCategoricalModuliSpace B S hS Z z → ∀ {Z' : AlgebraicSpaces B S hS}
      {z' : 𝒳 ⟶ fibredCategory B S hS Z'.obj} (k : Z ⟶ Z') (k' : Z' ⟶ Z),
      Nonempty (z ≫ (associatedMap B S hS k.hom).1 ≅ z') →
      Nonempty (z' ≫ (associatedMap B S hS k'.hom).1 ≅ z) → k ≫ k' = 𝟙 Z := by
    intro Z z hz Z' z' k k' ⟨ε⟩ ⟨ε'⟩
    refine eq_of_isCategoricalModuliSpace B S hS hz z _ _ ⟨?_⟩ ⟨?_⟩
    · change z ≫ (associatedMap B S hS (k.hom ≫ k'.hom)).1 ≅ z
      rw [associatedMap_comp]
      exact (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso ε _ ≪≫ ε'
    · change z ≫ (associatedMap B S hS (𝟙 Z.obj)).1 ≅ z
      rw [associatedMap_id_eq]
      exact Bicategory.rightUnitor z
  refine ⟨⟨h, h', hid hf h h' ⟨η⟩ ⟨η'⟩, hid hf' h' h ⟨η'⟩ ⟨η⟩⟩, ?_⟩
  exact hom_eq_of_hom₂ B S hS η.hom

end AlgebraicGeometry.Stack

end
