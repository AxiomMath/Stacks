module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Right derived functors of isomorphic functors

A total right derived functor of `F` along a localization `L` is also a total right derived
functor of any functor isomorphic to `F`, along the unit transported across the isomorphism.
Combined with `CategoryTheory.Functor.rightDerivedUnique` this identifies the right derived
functors of two isomorphic functors.

## Main results

* `Stacks.DerivedFunctorTransport.isLeftKanExtension_of_natIso`: the Kan-extension form.
* `Stacks.DerivedFunctorTransport.isRightDerivedFunctor_of_natIso`: the derived-functor form.
* `Stacks.DerivedFunctorTransport.mapHomotopyCategoryIso`: an isomorphism of additive functors
  induces one of the functors they induce on homotopy categories, which is what feeds the
  previous statement when the functor being derived is read on complexes.

## Implementation notes

`CategoryTheory.Functor.isLeftKanExtension_of_iso` transports a left Kan extension along an
isomorphism of the *extension*; what is needed here is the transport along an isomorphism of the
functor *being extended*, which is not in the library. It is proved directly from the universal
property: a morphism out of `⟨RF, e.inv ≫ α⟩` in the category of extensions of `F₀` is the same
datum as a morphism out of `⟨RF, α⟩` in the category of extensions of `F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctorTransport

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  {L : C ⥤ D} {F F₀ : C ⥤ H} {RF : D ⥤ H}

/-- **A left Kan extension of `F` is one of any functor isomorphic to `F`.** The unit is
transported across the isomorphism. -/
theorem isLeftKanExtension_of_natIso (e : F ≅ F₀) (α : F ⟶ L ⋙ RF)
    [RF.IsLeftKanExtension α] : RF.IsLeftKanExtension (e.inv ≫ α) := by
  obtain ⟨hu⟩ := (inferInstance : RF.IsLeftKanExtension α).nonempty_isUniversal
  refine ⟨⟨IsInitial.ofUniqueHom (fun G => StructuredArrow.homMk
    (hu.to (StructuredArrow.mk (e.hom ≫ G.hom))).right ?_) ?_⟩⟩
  · have h := (hu.to (StructuredArrow.mk (e.hom ≫ G.hom))).w
    dsimp at h ⊢
    rw [Category.assoc, h, Iso.inv_hom_id_assoc]
  · intro G m
    refine StructuredArrow.hom_ext _ _ (hu.hom_ext ?_)
    have hm := m.w
    have h := (hu.to (StructuredArrow.mk (e.hom ≫ G.hom))).w
    dsimp at hm h ⊢
    rw [h, ← hm, Category.assoc, Iso.hom_inv_id_assoc]

variable (W : MorphismProperty C) [L.IsLocalization W]

/-- **A total right derived functor of `F` is one of any functor isomorphic to `F`.** The unit
is transported across the isomorphism. -/
theorem isRightDerivedFunctor_of_natIso (e : F ≅ F₀) (α : F ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor α W] : RF.IsRightDerivedFunctor (e.inv ≫ α) W :=
  have := (inferInstance : RF.IsRightDerivedFunctor α W).isLeftKanExtension
  ⟨isLeftKanExtension_of_natIso e α⟩

/-- An isomorphism of additive functors induces an isomorphism of the functors they induce on
homotopy categories. -/
def mapHomotopyCategoryIso {ι : Type*} {V : Type*} [Category V] [Preadditive V]
    {V' : Type*} [Category V'] [Preadditive V'] {G G' : V ⥤ V'} [G.Additive] [G'.Additive]
    (e : G ≅ G') (c : ComplexShape ι) :
    G.mapHomotopyCategory c ≅ G'.mapHomotopyCategory c where
  hom := NatTrans.mapHomotopyCategory e.hom c
  inv := NatTrans.mapHomotopyCategory e.inv c
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id]

end Stacks.DerivedFunctorTransport

end
