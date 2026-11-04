module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Whiskering
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal.Existence

/-!
# Transferring coskeleta along a functor

Two ingredients used whenever a functor is applied degreewise to a simplicial object and the
canonical maps to the coskeleta are to be compared with those of the image.

## Main results

* `Stacks.CategoryTheory.Hypercovering.Construction.finCategoryTruncatedStructuredArrow`: the
  categories of structured arrows over the truncated simplex category are finite, so a functor
  preserving finite limits preserves the pointwise right Kan extensions computing coskeleta.
* `Stacks.CategoryTheory.Hypercovering.Construction.ranAdjunction_unit_whiskerRight`: the unit
  of a right-Kan-extension adjunction is carried by such a functor to the unit for the image,
  through the comparison isomorphism supplied by preservation.

## Implementation notes

The finiteness statement is a `FinCategory` structure rather than an instance: it is produced
from `Finite` facts about the truncated simplex category and is meant to be installed locally
with `letI` at the point of use, where the truncation level is fixed.

## References

* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
* [Stacks Project, Tag 0DB2](https://stacks.math.columbia.edu/tag/0DB2)
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryTheory.Hypercovering.Construction

/-- The categories of structured arrows over the `k`-truncated simplex category, which index the
matching objects in degree `k + 1`, are finite. -/
noncomputable abbrev finCategoryTruncatedStructuredArrow (k : ℕ) (Y : SimplexCategoryᵒᵖ) :
    FinCategory (StructuredArrow Y (SimplexCategory.Truncated.inclusion k).op) := by
  letI : Finite (SimplexCategory.Truncated k) :=
    SimplicialObject.Truncated.finite_truncated k
  letI : Finite (SimplexCategory.Truncated k)ᵒᵖ :=
    Finite.of_injective (fun a ↦ a.unop) (fun a b h ↦ by cases a; cases b; cases h; rfl)
  letI : ∀ X : (SimplexCategory.Truncated k)ᵒᵖ,
      Finite (Y ⟶ (SimplexCategory.Truncated.inclusion k).op.obj X) :=
    fun _ ↦ SimplicialObject.Truncated.finite_hom_op _ _
  letI : ∀ a b : (SimplexCategory.Truncated k)ᵒᵖ, Finite (a ⟶ b) := fun a b ↦ by
    let := SimplicialObject.Truncated.finite_hom_fullSubcategory b.unop a.unop
    exact SimplicialObject.Truncated.finite_hom_op a b
  have hobj : Finite (StructuredArrow Y (SimplexCategory.Truncated.inclusion k).op) := by
    refine Finite.of_injective
      (fun f ↦ (⟨f.right, f.hom⟩ : (X : (SimplexCategory.Truncated k)ᵒᵖ) ×
        (Y ⟶ (SimplexCategory.Truncated.inclusion k).op.obj X))) ?_
    rintro ⟨a, f, ha⟩ ⟨b, g, hb⟩ h
    obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.mp h
    obtain rfl := eq_of_heq h'
    cases a
    cases b
    rfl
  letI : ∀ a b : StructuredArrow Y (SimplexCategory.Truncated.inclusion k).op,
      Finite (a ⟶ b) := fun a b ↦
    Finite.of_injective CommaMorphism.right (fun f g h ↦ StructuredArrow.hom_ext _ _ h)
  exact { fintypeObj := Fintype.ofFinite _, fintypeHom := fun a b ↦ Fintype.ofFinite _ }

/-- The unit of a right-Kan-extension adjunction, whiskered with a functor preserving that right
Kan extension and followed by the comparison isomorphism, is the unit for the composite. -/
lemma ranAdjunction_unit_whiskerRight
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {E : Type*} [Category E] {G : Type*} [Category G]
    (L : A ⥤ E) (Q : E ⥤ B) (H : B ⥤ G)
    [∀ F : A ⥤ B, L.HasRightKanExtension F]
    [∀ F : A ⥤ G, L.HasRightKanExtension F]
    [H.PreservesRightKanExtension (L ⋙ Q) L] :
    Functor.whiskerRight ((Functor.ranAdjunction L B).unit.app Q) H ≫
      (H.rightKanExtensionCompIsoOfPreserves (L ⋙ Q) L).hom ≫
      (L.ran).map (Functor.associator L Q H).hom =
    (Functor.ranAdjunction L G).unit.app (Q ⋙ H) := by
  apply L.rightKanExtension_hom_ext
  ext a
  simp only [Functor.id_obj, Functor.comp_obj, Functor.ran, Functor.whiskeringLeft_obj_obj,
    Functor.ranAdjunction_unit_app, Functor.ranCounit, Functor.whiskerLeft_comp, Category.assoc,
    Functor.liftOfIsRightKanExtension_fac,
    Functor.rightKanExtensionCompIsoOfPreserves_hom_fac_assoc, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.comp_id, Category.id_comp, NatTrans.id_app]
  rw [← H.map_comp]
  simp

end Stacks.CategoryTheory.Hypercovering.Construction

end
