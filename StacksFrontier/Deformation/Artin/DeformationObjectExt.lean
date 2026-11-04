module

public import StacksFrontier.Deformation.Artin.Predeformation

/-!
# Extensionality for deformation objects

A `Deformation.Artin.DeformationObject` carries an Artinian local algebra, a point of `X`, an
arrow out of `x₀`, and two proofs. The two proofs are propositions, and the type of the arrow
depends on the point, so two deformation objects are equal as soon as the algebra and the point
agree and the arrows agree up to the resulting type equality.

## Main results

* `Deformation.Artin.deformationObject_ext`: deformation objects agreeing on algebra, point and
  arrow are equal.
-/

@[expose] public section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
  {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
  {hx₀ : q.obj x₀ = Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- Deformation objects agreeing on algebra, point and arrow are equal. -/
public theorem deformationObject_ext
    {a b : DeformationObject iΛ q x₀ hx₀}
    (halg : a.algebra = b.algebra) (hpoint : a.point = b.point)
    (harrow : HEq a.arrow b.arrow) : a = b := by
  cases a
  cases b
  cases halg
  cases hpoint
  cases eq_of_heq harrow
  rfl

end Deformation.Artin

end
