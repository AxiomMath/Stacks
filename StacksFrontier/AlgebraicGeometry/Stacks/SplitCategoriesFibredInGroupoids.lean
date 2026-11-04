module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Elements
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSectionIso
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangePoint
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Split
public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategoryIsCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.PresheafElementsStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverElementsPullback

/-!
# Split categories fibred in groupoids (Stacks 04SU)

The section of the chapter on algebraic stacks recalls the category `𝒮_F` attached to a presheaf
over the base category, and records how `F ↦ 𝒮_F` behaves:

* (a) a presheaf of groupoids `F` gives a category fibred in groupoids `𝒮_F` (Tag 0049);
* (b) a *split* category fibred in groupoids is one isomorphic to some `𝒮_F` (Tag 04TL);
* (c) every category fibred in groupoids is equivalent to a split one (Tag 02XY);
* (d) for a presheaf of sets `F`, `𝒮_F` is fibred in sets (Tags 0043, 04TM);
* (e) `F ↦ 𝒮_F` is fully faithful on presheaves of sets (Tag 02Y2): 1-morphisms over the base
  between `𝒮_F` and `𝒮_G` are exactly the maps of presheaves `F ⟶ G`, and the only 2-morphisms
  between 1-morphisms into a category fibred in sets are identities;
* (f) `𝒮_{F × G} = 𝒮_F × 𝒮_G` and `𝒮_{F ×_H G} = 𝒮_F ×_{𝒮_H} 𝒮_G`, the right hand sides being
  2-fibre products over the base (Tag 0040);
* (g) `𝒮_{h_X}` is the slice category over `X` (Tag 0044).

The source states all of this over `(Sch/S)_fppf`; everything here is stated over an arbitrary
base category `C`, of which the big fppf site of `S` is a special case.

## Main results

* `CategoryTheory.PresheafOfCategories.elementsMapEquiv`: (e), maps of presheaves are the
  1-morphisms over `C` between the categories of elements.
* `CategoryTheory.TwoFibreProductOver.exists_elementsOp_equivalence_of_isPullback`: (f) for a
  fibre product of presheaves of sets.
* `CategoryTheory.TwoFibreProductOver.exists_elementsOp_equivalence_of_isLimit_binaryFan`: (f)
  for a product of presheaves of sets.

The other assertions are recorded against Tag 04SU on the declarations that prove them.

## Implementation notes

For a presheaf of groupoids, (a)-(c) use the category `CategoryTheory.presheafOfGroupoids F`
attached to it by Tag 02XV. Two models of `𝒮_F` for a presheaf of sets occur in the library, and
each assertion is stated in the model its existing proof uses. Assertions (d) and (e) use the
category attached by Tag 02XV to `F` regarded as a presheaf of discrete categories,
`CategoryTheory.PresheafOfCategories.discreteProjection`. Assertions (f) and (g) use Mathlib's
category of elements, `(F.Elements)ᵒᵖ` with structure functor
`(CategoryOfElements.π F).leftOp`, whose morphisms are morphisms of the base satisfying an
equation, so that the comparison functors of (f) are strictly over `C` and strictly compatible
with the two projections, by `rfl`. The 2-fibre product of (f) is the explicit one over `C`,
`CategoryTheory.TwoFibreProductOver` (Tag 0040).

## References

* [Stacks Project, Tag 04SU](https://stacks.math.columbia.edu/tag/04SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

add_to_stacks 04SU "(a) the category fibred in groupoids S_F attached to a presheaf of groupoids F"
  CategoryTheory.presheafOfGroupoids
add_to_stacks 04SU "(a) S_F is fibred in groupoids"
  CategoryTheory.isFiberedInGroupoids_presheafOfGroupoids
add_to_stacks 04SU "(b) split categories fibred in groupoids: isomorphic over the base to some S_F"
  CategoryTheory.Functor.IsSplitFiberedInGroupoids
add_to_stacks 04SU "(c) every category fibred in groupoids is equivalent to a split one"
  CategoryTheory.Functor.exists_isFibredEquivalenceOver_presheafOfGroupoids
add_to_stacks 04SU "(d) for a presheaf of sets F, S_F is fibred in sets"
  CategoryTheory.PresheafOfCategories.isFiberedInSets_discreteProjection
add_to_stacks 04SU "(e) the only 2-morphisms into a category fibred in sets are identities"
  CategoryTheory.Functor.twoMorphisms_are_identity
add_to_stacks 04SU "(g) S_{h_X} is the slice category over X"
  CategoryTheory.overEquivElementsOp
add_to_stacks 04SU "(g) the identification of S_{h_X} with the slice category is over the base"
  CategoryTheory.overEquivElementsOpForget

namespace CategoryTheory.PresheafOfCategories

variable {C : Type u} [Category.{v} C]

/-- **Tag 04SU (e).** The rule `F ↦ 𝒮_F` is fully faithful on presheaves of sets: maps of
presheaves `F ⟶ G` are in bijection with the 1-morphisms `𝒮_F ⥤ 𝒮_G` strictly over `C`, by
`m ↦ El m`. -/
@[stacks 04SU "(e) maps of presheaves F ⟶ G are the 1-morphisms S_F ⥤ S_G over the base"]
def elementsMapEquiv (F G : Cᵒᵖ ⥤ Type v) :
    (F ⟶ G) ≃ {θ : (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
        (presheafOfCategories (G ⋙ typeToCat)).obj //
      θ ⋙ discreteProjection G = discreteProjection F} where
  toFun m := ⟨elementsMap m, elementsMap_comp_eq m⟩
  invFun θ := natTransOfBasedFunctor θ.1 θ.2
  left_inv m := natTransOfBasedFunctor_elementsMap m
  right_inv θ := Subtype.ext (eq_of_sections_eq _ _ (elementsMap_comp_eq _) θ.2 fun t => by
    obtain ⟨V, ⟨g⟩⟩ := t
    rfl)

end CategoryTheory.PresheafOfCategories

namespace CategoryTheory.TwoFibreProductOver

variable {C : Type u} [Category.{v} C] {F G H P : Cᵒᵖ ⥤ Type w}

/-- **Tag 04SU (f), fibre products.** For maps `α : F ⟶ H` and `β : G ⟶ H` of presheaves of sets
and a fibre product `P = F ×_H G`, the category of elements `𝒮_P` is equivalent to the 2-fibre
product `𝒮_F ×_{𝒮_H} 𝒮_G` over `C`, by an equivalence which is strictly over `C` and whose
composites with the two projections are the 1-morphisms induced by the projections of `P`. -/
@[stacks 04SU "(f) S_{F ×_H G} = S_F ×_{S_H} S_G for maps F → H ← G of presheaves of sets"]
theorem exists_elementsOp_equivalence_of_isPullback {α : F ⟶ H} {β : G ⟶ H} {pF : P ⟶ F}
    {pG : P ⟶ G} (h : IsPullback pF pG α β) :
    ∃ e : P.Elementsᵒᵖ ≌
        TwoFibreProductOver (CategoryOfElements.π F).leftOp (CategoryOfElements.π G).leftOp
          (CategoryOfElements.π H).leftOp (CategoryOfElements.map α).op
          (CategoryOfElements.map β).op,
      e.functor ⋙ structureFunctor _ _ _ _ _ = (CategoryOfElements.π P).leftOp ∧
      e.functor ⋙ fst _ _ _ _ _ = (CategoryOfElements.map pF).op ∧
      e.functor ⋙ snd _ _ _ _ _ = (CategoryOfElements.map pG).op :=
  ⟨(elementsPullback h).asEquivalence, elementsPullback_comp_structureFunctor h,
    elementsPullback_comp_fst h, elementsPullback_comp_snd h⟩

/-- **Tag 04SU (f), products.** For a product `P = F × G` of presheaves of sets, the category of
elements `𝒮_P` is equivalent to the 2-fibre product `𝒮_F ×_C 𝒮_G` over `C` (taken along the two
structure functors and the identity of `C`), by an equivalence which is strictly over `C` and
whose composites with the two projections are the 1-morphisms induced by the projections of
`P`. -/
@[stacks 04SU "(f) S_{F × G} = S_F ×_C S_G for presheaves of sets F, G"]
theorem exists_elementsOp_equivalence_of_isLimit_binaryFan {pF : P ⟶ F} {pG : P ⟶ G}
    (h : IsLimit (BinaryFan.mk pF pG)) :
    ∃ e : P.Elementsᵒᵖ ≌
        TwoFibreProductOver (CategoryOfElements.π F).leftOp (CategoryOfElements.π G).leftOp
          (𝟭 C) (CategoryOfElements.π F).leftOp (CategoryOfElements.π G).leftOp,
      e.functor ⋙ structureFunctor _ _ _ _ _ = (CategoryOfElements.π P).leftOp ∧
      e.functor ⋙ fst _ _ _ _ _ = (CategoryOfElements.map pF).op ∧
      e.functor ⋙ snd _ _ _ _ _ = (CategoryOfElements.map pG).op :=
  have := isEquivalence_elementsProd h
  ⟨(elementsProd pF pG).asEquivalence, elementsProd_comp_structureFunctor,
    elementsProd_comp_fst, elementsProd_comp_snd⟩

end CategoryTheory.TwoFibreProductOver
