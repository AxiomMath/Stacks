module

public import StacksFrontier.CategoryTheory.Adjunction.RestrictEquivalence
public import StacksFrontier.CategoryTheory.Triangulated.LinearTriangulatedEquivalence
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Restricting an adjunction of linear triangulated categories to an equivalence

Let `F ⊣ G` be an adjunction between `R`-linear pretriangulated categories `C` and `D`, and let
`P` and `Q` be triangulated subcategories of `C` and `D` carried into each other by `F` and `G`.
If the unit is invertible on `P` and `G` reflects isomorphisms between objects of `Q`, the
adjunction restricts to an equivalence `P ≌ Q` whose functor is `F` on `P`. When `F` commutes
with the shifts, is triangulated and is `R`-linear, so is this functor, because the inclusion of
`Q` is fully faithful, triangulated and commutes with the shifts. The restricted equivalence is
then an equivalence of `R`-linear triangulated categories.

## Main definitions

* `CategoryTheory.Adjunction.restrictLinearTriangulatedEquivalence`: **the restricted
  equivalence `P ≌ Q` as an equivalence of `R`-linear triangulated categories.**

## Main results

* `CategoryTheory.Adjunction.restrictLinearTriangulatedEquivalence_equivalence`: its underlying
  equivalence is `Adjunction.restrictEquivalence`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

open Limits Pretriangulated

universe w v₁ v₂ u₁ u₂

variable (R : Type w) [Ring R]
  {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {P : ObjectProperty C} {Q : ObjectProperty D}
  [P.IsTriangulated] [Q.IsTriangulated] [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
  (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ Y, Q Y → P (G.obj Y))
  (hu : ∀ X, P X → IsIso (adj.unit.app X))
  (hr : ∀ ⦃Y Y' : D⦄ (g : Y ⟶ Y'), Q Y → Q Y' → IsIso (G.map g) → IsIso g)

/-- The functor of the restricted equivalence commutes with the shifts, compatibly with the
identification of its composite with the inclusion of `Q` with `F` on `P`. -/
@[instance_reducible]
instance restrictEquivalence_functor_commShift :
    (adj.restrictEquivalence hF hG hu hr).functor.CommShift ℤ :=
  Functor.CommShift.ofComp (adj.restrictEquivalenceFunctorCompι hF hG hu hr) ℤ

/-- The identification of the functor of the restricted equivalence followed by the inclusion of
`Q` with `F` on `P` commutes with the shifts. -/
instance restrictEquivalenceFunctorCompι_hom_commShift :
    NatTrans.CommShift (adj.restrictEquivalenceFunctorCompι hF hG hu hr).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- **The functor of the restricted equivalence is triangulated.** -/
instance restrictEquivalence_functor_isTriangulated :
    (adj.restrictEquivalence hF hG hu hr).functor.IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right
    (adj.restrictEquivalenceFunctorCompι hF hG hu hr)).2 inferInstance

/-- **The functor of the restricted equivalence is `R`-linear.** -/
instance restrictEquivalence_functor_linear :
    (adj.restrictEquivalence hF hG hu hr).functor.Linear R where
  map_smul f r := by
    ext
    exact F.map_smul r f.hom

/-- **An adjunction of `R`-linear triangulated categories whose left adjoint commutes with the
shifts, is triangulated and is `R`-linear, whose unit is invertible on the triangulated
subcategory `P` and whose right adjoint reflects isomorphisms between objects of the triangulated
subcategory `Q`, restricts to an equivalence `P ≌ Q` of `R`-linear triangulated categories.** -/
def restrictLinearTriangulatedEquivalence :
    LinearTriangulatedEquivalence R P.FullSubcategory Q.FullSubcategory where
  equivalence := adj.restrictEquivalence hF hG hu hr
  commShift := adj.restrictEquivalence_functor_commShift hF hG hu hr
  isTriangulated := adj.restrictEquivalence_functor_isTriangulated hF hG hu hr
  linear := adj.restrictEquivalence_functor_linear R hF hG hu hr

/-- The underlying equivalence of `restrictLinearTriangulatedEquivalence` is the restricted
equivalence. -/
theorem restrictLinearTriangulatedEquivalence_equivalence :
    (adj.restrictLinearTriangulatedEquivalence R hF hG hu hr).equivalence =
      adj.restrictEquivalence hF hG hu hr :=
  rfl

end CategoryTheory.Adjunction

end
