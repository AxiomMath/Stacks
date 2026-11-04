module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.InternalPolynomialEvaluation

/-!
# The transported and the sectionwise ring object of an inverse-image sheaf of rings agree

Let `Φ : Sh(D) ⥤ Sh(C)` be a finite-product-preserving functor between categories of sheaves of
sets and let `𝒪` be a sheaf of commutative rings on `(D, K)`. There are two ways to make the
sheaf of sets `Φ(𝒪)` a commutative ring object:

* **transported**: `Φ` preserves finite products, hence is braided monoidal, hence carries the
  ring object `𝒪` to a ring object `Φ(𝒪)` whose operations are the images of the operations of
  `𝒪`, conjugated by the product comparison. This is
  `CategoryTheory.Functor.commRingObjObj`.
* **sectionwise**: the inverse-image sheaf of commutative rings
  `Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf` has `Φ(𝒪)` as its underlying sheaf of
  sets on the nose, so it makes `Φ(𝒪)` a ring object by its own sectionwise operations. This is
  `Stacks.sheafCommRingObj` of the inverse image.

This file proves that the two structures are equal.

## Main results

* `Stacks.Sheaves.ToposPullback.commRingObjObj_eq_sheafCommRingObj`: the two commutative ring
  object structures on `Φ(𝒪)` coincide.
* `Stacks.Sheaves.ToposPullback.commRingObj_eq_of_add_eq_of_mul_eq`: a commutative ring object
  structure is determined by its internal addition and multiplication.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CommRingObj Obj

universe ww ww' vv uu vv' uu' v u

namespace Stacks.Sheaves.ToposPullback

/-! ### A commutative ring object is determined by its addition and its multiplication -/

section Ext

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- A ring object structure is determined by its underlying additive group object and its
underlying monoid object: the two distributivity fields are propositions, and so is
commutativity of the addition. -/
theorem ringObj_eq_of_addGrpObj_eq_of_monObj_eq {R : C} (h₁ h₂ : RingObj R)
    (hadd : h₁.toAddGrpObj = h₂.toAddGrpObj) (hmul : h₁.toMonObj = h₂.toMonObj) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hadd
  cases hmul
  congr 1

/-- A commutative ring object structure is determined by its underlying ring object structure:
commutativity of the multiplication is a proposition. -/
theorem commRingObj_eq_of_ringObj_eq {R : C} (h₁ h₂ : CommRingObj R)
    (h : h₁.toRingObj = h₂.toRingObj) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases h
  congr 1

/-- A commutative ring object structure is determined by its internal addition and
multiplication. -/
theorem commRingObj_eq_of_add_eq_of_mul_eq {R : C} (h₁ h₂ : CommRingObj R)
    (hadd : AddMonObj.add (self := h₁.toRingObj.toAddGrpObj.toAddMonObj) =
      AddMonObj.add (self := h₂.toRingObj.toAddGrpObj.toAddMonObj))
    (hmul : MonObj.mul (self := h₁.toRingObj.toMonObj) =
      MonObj.mul (self := h₂.toRingObj.toMonObj)) :
    h₁ = h₂ :=
  commRingObj_eq_of_ringObj_eq h₁ h₂
    (ringObj_eq_of_addGrpObj_eq_of_monObj_eq _ _
      (AddGrpObj.ext _ _ (AddMonObj.ext _ _ hadd)) (MonObj.ext _ _ hmul))

end Ext

/-! ### The two ring objects of an inverse image -/

section Pullback

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ] [Φ.Braided]

attribute [local instance] Stacks.sheafCommRingObj

omit [J.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})] in
/-- The lax monoidal comparison of a finite-product-preserving functor is a section of the
product comparison: the first is the inverse of the second. -/
theorem mu_comp_prodComparison (A B : Sheaf K (Type ww')) :
    Functor.LaxMonoidal.μ Φ A B ≫ Limits.prodComparison Φ A B = 𝟙 _ := by
  have h : Limits.prodComparison Φ A B = Functor.OplaxMonoidal.δ Φ A B :=
    (Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory Φ A B).symm
  rw [h]
  exact Functor.Monoidal.μ_δ Φ A B

variable (O : Sheaf K CommRingCat.{ww'})

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- The commutative ring object structure that a finite-product-preserving functor `Φ` transports
from a sheaf of commutative rings `𝒪` to the sheaf of sets `Φ(𝒪)` is the structure that the
inverse-image sheaf of commutative rings puts on its own underlying sheaf of sets. -/
theorem commRingObjObj_eq_sheafCommRingObj :
    Φ.commRingObjObj (Stacks.underlyingRingSheaf K O) =
      Stacks.sheafCommRingObj J (pullbackCommRingSheaf J Φ O) := by
  have key {A : Sheaf K (Type ww')} (f : A ⊗ A ⟶ A) (g : Φ.obj A ⊗ Φ.obj A ⟶ Φ.obj A)
      (h : Φ.map f = Limits.prodComparison Φ A A ≫ g) :
      Functor.LaxMonoidal.μ Φ A A ≫ Φ.map f = g := by
    rw [h]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g) (mu_comp_prodComparison J Φ A A)).trans (Category.id_comp _))
  refine commRingObj_eq_of_add_eq_of_mul_eq _ _ ?_ ?_
  · exact key _ _ (ringAdd_map_aux' J Φ (Stacks.SheafOfModules.Tensor.ringSheaf O))
  · exact key _ _ (ringMul_map_aux' J Φ (Stacks.SheafOfModules.Tensor.ringSheaf O))

end Pullback

end Stacks.Sheaves.ToposPullback

end
