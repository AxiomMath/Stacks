module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import StacksFrontier.Cotangent.StandardResolutionOverPolynomialBase

/-!
# Distinguished triangles of the bounded below derived category from unbounded ones

The bounded below derived category `DerivedCategory.Plus C` is a full triangulated subcategory of
`DerivedCategory C`, whose distinguished triangles are those whose image in `DerivedCategory C`
is distinguished. So a distinguished triangle of `DerivedCategory C` whose three objects are
isomorphic to images of objects of `DerivedCategory.Plus C` yields a distinguished triangle of
`DerivedCategory.Plus C` on those objects.

## Main results

* `DerivedCategory.Plus.exists_distinguished_of_ι_objIso`: a distinguished triangle of
  `DerivedCategory C` with objects isomorphic to `Plus.ι.obj A`, `Plus.ι.obj B`, `Plus.ι.obj D`
  gives a distinguished triangle `A ⟶ B ⟶ D ⟶ A⟦1⟧` of `DerivedCategory.Plus C`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A distinguished triangle of `DerivedCategory C` whose objects are isomorphic to the images of
three objects `A`, `B`, `D` of `DerivedCategory.Plus C` yields, for suitable morphisms, a
distinguished triangle `A ⟶ B ⟶ D ⟶ A⟦1⟧` of `DerivedCategory.Plus C`. -/
theorem exists_distinguished_of_ι_objIso (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (A B D : Plus C) (a : Plus.ι.obj A ≅ T.obj₁)
    (b : Plus.ι.obj B ≅ T.obj₂) (c : Plus.ι.obj D ≅ T.obj₃) :
    ∃ (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (Plus C) := by
  obtain ⟨f, g, h, hfgh⟩ := exists_distinguished_of_objIso T hT _ _ _ a b c
  refine ⟨Plus.ι.preimage f, Plus.ι.preimage g,
    Plus.ι.preimage (h ≫ (Plus.ι.commShiftIso (1 : ℤ)).inv.app A), ?_⟩
  change Plus.ι.mapTriangle.obj _ ∈ distTriang (DerivedCategory C)
  rw [Functor.mapTriangle_obj]
  dsimp only [Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃, Triangle.mk_obj₁]
  rw [Functor.map_preimage, Functor.map_preimage, Functor.map_preimage, Category.assoc,
    Iso.inv_hom_id_app]
  exact (Category.comp_id h).symm ▸ hfgh

end DerivedCategory.Plus
