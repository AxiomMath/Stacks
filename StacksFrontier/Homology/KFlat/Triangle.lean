module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# K-flat complexes in distinguished triangles

Let `R` be a commutative ring. K-flatness of complexes of `R`-modules satisfies the
two-out-of-three property for distinguished triangles in the homotopy category
`K(Mod(R))`: whenever two of the three vertices of a distinguished triangle are K-flat,
so is the remaining one.

## Main results

* `CochainComplex.KFlat.kFlat_two_out_of_three_of_distTriang`: if two vertices of a
  distinguished triangle in the homotopy category of cochain complexes of `R`-modules are
  K-flat, then so is the third.

## Implementation notes

The established tensor product of complexes of modules is used here over a commutative ring.
The three objects of the triangle are represented by cochain complexes, as the objects of the
homotopy category are definitionally those complexes.

The proof tensors the given distinguished triangle with a fixed acyclic complex `L`. That
`L ⊗ -` is an exact functor of triangulated categories on `K(Mod(R))` is
`TotalTensorComplex.tleft_isTriangulated` (Stacks Tag 064J), the `ModuleCat R`
specialization of the general statement for a preadditive monoidal category. K-flatness of
a vertex is then exactly the statement that the corresponding vertex of the image triangle
lies in the acyclic subcategory, and the three implications are the three closure
properties `ObjectProperty.ext_of_isTriangulatedClosed₁`, `₂`, `₃` of that subcategory.

## References

* [The Stacks Project, Tag 06Y2](https://stacks.math.columbia.edu/tag/06Y2)
-/

open CategoryTheory Pretriangulated MonoidalCategory

universe u

namespace CochainComplex.KFlat

/-- K-flatness is a two-out-of-three property in a distinguished triangle of the homotopy
category. -/
@[stacks 06Y2]
theorem kFlat_two_out_of_three_of_distTriang
    {R : Type u} [CommRing R] {K₁ K₂ K₃ : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K₁ ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K₂)
    (g : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K₂ ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K₃)
    (h : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K₃ ⟶
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))) :
    (K₂.KFlat → K₃.KFlat → K₁.KFlat) ∧
      (K₁.KFlat → K₃.KFlat → K₂.KFlat) ∧
      (K₁.KFlat → K₂.KFlat → K₃.KFlat) := by
  let T := Triangle.mk f g h
  have hq := fun K : CochainComplex (ModuleCat.{u} R) ℤ =>
    HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K
  refine ⟨?_, ?_, ?_⟩ <;> intro ha hb L hL <;>
  · obtain ⟨e, he⟩ := TotalTensorComplex.tleft_isTriangulated L
    let := e
    let := he
    have hTL : (Tleft L).mapTriangle.obj T ∈
        distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
      (Tleft L).map_distinguished T hT
    refine (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 ?_
    have h₁ := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (ha L hL)
    have h₂ := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hb L hL)
    first
    | exact ObjectProperty.ext_of_isTriangulatedClosed₁
        (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)) _ hTL h₁ h₂
    | exact ObjectProperty.ext_of_isTriangulatedClosed₂
        (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)) _ hTL h₁ h₂
    | exact ObjectProperty.ext_of_isTriangulatedClosed₃
        (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)) _ hTL h₁ h₂

end CochainComplex.KFlat

end
