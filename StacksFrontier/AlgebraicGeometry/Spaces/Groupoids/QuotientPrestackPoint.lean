module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack

/-!
# Objects of a fibre of the pointwise groupoid fibration

Let `B` be an algebraic space over a scheme `S` of a big fppf site and let `G` be a groupoid in
algebraic spaces over `B`. The fibre of the pointwise groupoid fibration of `G` over a test object
`T` of the site is, up to the universe lift, the groupoid obtained by evaluating `G` at `T`. This
file names the object of that fibre determined by a `T`-point of the object space of `G`, and
records that every object of the fibre arises this way.

## Main definitions

* `AlgebraicGeometry.Stack.prestackPoint`: the object of the fibre of the pointwise groupoid
  fibration over a test object determined by a point of the object space.

## Main results

* `AlgebraicGeometry.Stack.exists_prestackPoint`: every object of a fibre of the pointwise
  groupoid fibration is determined by a point of the object space.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bs : AlgebraicSpaces C S hS}

/-- The object of the fibre of the pointwise groupoid fibration over a test object determined by
a point of the object space. -/
abbrev prestackPoint (G : GroupoidInAlgebraicSpaces C S hS Bs)
    (T : BigFppfOver C S hS) (w : G.objects.obj.obj (op T)) :
    (quotientPrestack G).p.Fiber T :=
  ⟨(quotientPrestackEquivalence G).functor.obj ⟨T, w⟩, rfl⟩

/-- Every object of a fibre of the pointwise groupoid fibration is determined by a point of the
object space. -/
lemma exists_prestackPoint (G : GroupoidInAlgebraicSpaces C S hS Bs)
    (T : BigFppfOver C S hS) (z : (quotientPrestack G).p.Fiber T) :
    ∃ w, z = prestackPoint G T w := by
  rcases z with ⟨⟨T', w⟩, hz⟩
  change T' = T at hz
  subst T
  exact ⟨w, rfl⟩

end AlgebraicGeometry.Stack

end
