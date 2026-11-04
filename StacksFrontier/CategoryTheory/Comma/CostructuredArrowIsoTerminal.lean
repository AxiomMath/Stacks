module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Terminal objects presented by an isomorphism

Two small facts about terminal objects used when a site is read at a representable object.

* A costructured arrow `S(Y) ⟶ X` which is an *isomorphism* is terminal in
  `CategoryTheory.CostructuredArrow S X`, for `S` fully faithful.  Mathlib's
  `CategoryTheory.CostructuredArrow.mkIdTerminal` is the case `X = S(Y)` with the identity; the
  general case is what an étale chart presented by an isomorphism `F ≅ yoneda.obj T` needs,
  since there the arrow is the inverse of that isomorphism and not an identity.
* An object of a full subcategory which is terminal in the ambient category is terminal in the
  full subcategory.

## Main results

* `CategoryTheory.CostructuredArrow.mkIsoTerminal`
* `CategoryTheory.ObjectProperty.isTerminal_of_isTerminal_obj`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace CostructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **A costructured arrow which is an isomorphism is terminal.**  For a fully faithful `S` and
an isomorphism `h : S(Y) ⟶ X`, the object `mk h` of `CostructuredArrow S X` is terminal: a
morphism to it out of `S(Y') ⟶ X` is a morphism `Y' ⟶ Y` of `C` whose image under `S` is the
given arrow followed by `h⁻¹`, and `S` being fully faithful there is exactly one.

This generalizes `CategoryTheory.CostructuredArrow.mkIdTerminal`, which is the case `h = 𝟙`. -/
def mkIsoTerminal {S : C ⥤ D} [S.Full] [S.Faithful] {Y : C} {X : D} (h : S.obj Y ⟶ X)
    [IsIso h] : IsTerminal (CostructuredArrow.mk h) where
  lift c := CostructuredArrow.homMk (S.preimage (c.pt.hom ≫ inv h)) (by simp)
  uniq := by
    rintro c m -
    ext
    apply S.map_injective
    have hm : S.map m.left ≫ h = c.pt.hom := CostructuredArrow.w m
    simp only [homMk_left, S.map_preimage]
    rw [← hm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end CostructuredArrow

/-- **An object of a slice category whose structure morphism is an isomorphism is terminal.**
The slice `Over X` is `CostructuredArrow (𝟭 C) X` and the identity functor is fully faithful, so
this is `CategoryTheory.CostructuredArrow.mkIsoTerminal`. -/
def Over.isTerminalMkOfIsIso {C : Type u₁} [Category.{v₁} C] {X A : C} (f : A ⟶ X) [IsIso f] :
    IsTerminal (Over.mk f) :=
  CostructuredArrow.mkIsoTerminal (S := 𝟭 C) f

namespace ObjectProperty

variable {C : Type u₁} [Category.{v₁} C] {P : ObjectProperty C}

/-- **An object of a full subcategory which is terminal in the ambient category is terminal in
the full subcategory**: the morphisms are the same. -/
def isTerminal_of_isTerminal_obj (A : P.FullSubcategory) (h : IsTerminal A.obj) :
    IsTerminal A :=
  IsTerminal.ofUniqueHom (fun B => ObjectProperty.homMk (h.from B.obj))
    (fun _ m => ObjectProperty.hom_ext _ (h.hom_ext m.hom (h.from _)))

end ObjectProperty

end CategoryTheory

end
