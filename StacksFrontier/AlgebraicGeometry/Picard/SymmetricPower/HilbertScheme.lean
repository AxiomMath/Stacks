module

public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.HilbertPresheaf

/-!
# The Hilbert scheme of points, when it exists

When the Hilbert presheaf `hilbPresheaf X d` is representable, its representing scheme is the
Hilbert scheme of points `Hilb^d_{X/S}`, which represents the Hilbert functor of points of rank
`d` in the sense of `Stacks.Hilbert.RepresentsHilbertFunctorOfRank`.
These names are used by the consumers of the Hilbert scheme (the Picard scheme of a curve,
Stacks Tag 0B9X; the geometry of `Hilb^d`, Stacks Tag 0B9I).

## Main definitions

* `Stacks.Hilbert.hilbScheme`: the representing scheme of `hilbPresheaf X d`.
* `Stacks.Hilbert.hilbOver`: the Hilbert scheme viewed as a scheme over `S`.
* `Stacks.Hilbert.representsHilbOver`: `hilbOver X d` represents the Hilbert functor of points of
  rank `d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}} (X : Over S) (d : ℕ) [(hilbPresheaf X d).IsRepresentable]

/-- **The Hilbert scheme of points** `Hilb^d_{X/S}`, when the Hilbert presheaf is
representable. -/
def hilbScheme : Scheme.{u} := (hilbPresheaf X d).reprX

/-- The Hilbert scheme of points as a scheme over `S`, through the structure morphism of its
universal pair. -/
def hilbOver : Over S := Over.mk (repStructure (hilbPresheaf X d).representableBy)

/-- **The Hilbert scheme of points represents the Hilbert functor of points.** -/
def representsHilbOver : RepresentsHilbertFunctorOfRank X (hilbOver X d) d :=
  representsOfRepresentableBy (hilbPresheaf X d).representableBy

/-- The underlying scheme of `hilbOver X d` is `hilbScheme X d`. -/
theorem hilbOver_left : (hilbOver X d).left = hilbScheme X d := rfl

end Stacks.Hilbert

end
