module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# Inverse images of abelian sheaves along equivalences

If the inverse image of sheaves of sets along a morphism of topoi is an equivalence, then so is the
inverse image of abelian sheaves `CategoryTheory.Sites.abelianInverseImage`.
-/

@[expose] public section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

namespace CategoryTheory.Sites

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe v u v' u' w w'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- **The inverse image of abelian sheaves along a morphism of topoi whose inverse image of
sheaves of sets is an equivalence is an equivalence**: it is the conjugate, by the identification
of abelian sheaves with commutative group objects, of the image under
`CategoryTheory.Equivalence.mapCommGrp` of the inverse image of sheaves of sets. -/
theorem isEquivalence_abelianInverseImage_of_isEquivalence [f.inverseImage.IsEquivalence] :
    (abelianInverseImage f).IsEquivalence := by
  let : f.inverseImage.Braided := .ofChosenFiniteProducts _
  let : f.inverseImage.asEquivalence.functor.Braided := .ofChosenFiniteProducts _
  let : f.inverseImage.asEquivalence.inverse.Braided := .ofChosenFiniteProducts _
  let E : Sheaf K AddCommGrpCat.{w'} ≌ Sheaf J AddCommGrpCat.{w} :=
    (AbelianSheaf.equivalence K).trans
      ((Equivalence.mapCommGrp f.inverseImage.asEquivalence).trans
        (AbelianSheaf.equivalence J).symm)
  have h : E.functor = abelianInverseImage f := rfl
  rw [← h]
  infer_instance

end CategoryTheory.Sites
