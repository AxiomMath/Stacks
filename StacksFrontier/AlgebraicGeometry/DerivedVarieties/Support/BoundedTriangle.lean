module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic

/-!
# Lifting a distinguished triangle to the bounded derived category

A triangle in the derived category of an abelian category all three of whose vertices are bounded
lifts to a triangle in the bounded derived category, and the lift is distinguished as soon as the
original triangle is. This is the standard device for transporting an induction over distinguished
triangles from the ambient derived category to its bounded subcategory.

## Main definitions

* `AlgebraicGeometry.liftBoundedTriangle`: the lifted triangle.

## Main results

* `AlgebraicGeometry.liftBoundedTriangle_distinguished`: the lift of a distinguished triangle is
  distinguished.

## Implementation notes

The connecting map of the lifted triangle is the original connecting map followed by the inverse
of the shift isomorphism of the inclusion `DerivedCategory.Bounded.ι`, which is exactly what makes
`DerivedCategory.Bounded.ι.mapTriangle` send the lift back to the original triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace AlgebraicGeometry

/-- A triangle of the derived category with bounded vertices, regarded as a triangle of the
bounded derived category. -/
public noncomputable def liftBoundedTriangle
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (T : Triangle (DerivedCategory A))
    (h₁ : DerivedCategory.TStructure.t.bounded T.obj₁)
    (h₂ : DerivedCategory.TStructure.t.bounded T.obj₂)
    (h₃ : DerivedCategory.TStructure.t.bounded T.obj₃) :
    Triangle (DerivedCategory.Bounded A) := by
  let X : DerivedCategory.Bounded A := ⟨T.obj₁, h₁⟩
  let Y : DerivedCategory.Bounded A := ⟨T.obj₂, h₂⟩
  let Z : DerivedCategory.Bounded A := ⟨T.obj₃, h₃⟩
  exact Triangle.mk (X := X) (Y := Y) (Z := Z)
    (ObjectProperty.homMk T.mor₁) (ObjectProperty.homMk T.mor₂)
    (ObjectProperty.homMk
      (T.mor₃ ≫ (DerivedCategory.Bounded.ι.commShiftIso 1).inv.app X))

/-- The lift of a distinguished triangle with bounded vertices is distinguished in the bounded
derived category. -/
public lemma liftBoundedTriangle_distinguished
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (T : Triangle (DerivedCategory A))
    (h₁ : DerivedCategory.TStructure.t.bounded T.obj₁)
    (h₂ : DerivedCategory.TStructure.t.bounded T.obj₂)
    (h₃ : DerivedCategory.TStructure.t.bounded T.obj₃)
    (hT : T ∈ distTriang (DerivedCategory A)) :
    liftBoundedTriangle T h₁ h₂ h₃ ∈ distTriang (DerivedCategory.Bounded A) := by
  cases T with
  | mk' X Y Z f g h =>
    apply (DerivedCategory.Bounded.ι.map_distinguished_iff _).1
    have hm : DerivedCategory.Bounded.ι.mapTriangle.obj
        (liftBoundedTriangle (Triangle.mk' X Y Z f g h) h₁ h₂ h₃) =
        Triangle.mk f g h := by
      simp [liftBoundedTriangle, Functor.mapTriangle, Category.assoc]
    rw [hm]
    exact hT

end AlgebraicGeometry

end
