module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay

/-!
# Gorenstein morphisms are Cohen--Macaulay

A Gorenstein morphism of schemes is a Cohen--Macaulay morphism: it is flat, and the local ring
of the fibre at each point of the source, being a Gorenstein local ring, is Cohen--Macaulay.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isCohenMacaulayAt_of_isGorensteinAt`: a morphism Gorenstein at a
  point is Cohen--Macaulay there.
* `AlgebraicGeometry.Scheme.Hom.isCohenMacaulay_of_isGorenstein`: a Gorenstein morphism is
  Cohen--Macaulay.

## References

* [Stacks Project, Tag 0C06](https://stacks.math.columbia.edu/tag/0C06)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks Project, Tag 0C06.** A morphism with locally Noetherian fibres that is Gorenstein
at a point of its source is Cohen--Macaulay at that point. -/
public theorem isCohenMacaulayAt_of_isGorensteinAt
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) {x : X} (h : IsGorensteinAt f hf x) :
    IsCohenMacaulayAt f hf x :=
  let := hf (f x)
  ⟨h.1, Dualizing.IsGorensteinLocalRing.isCohenMacaulayLocalRing _ h.2⟩

/-- **Stacks Project, Tag 0C06.** A Gorenstein morphism is Cohen--Macaulay. -/
@[stacks 0C06]
public theorem isCohenMacaulay_of_isGorenstein
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (h : IsGorenstein f hf) :
    IsCohenMacaulay f hf :=
  fun x => isCohenMacaulayAt_of_isGorensteinAt f hf (h x)

end AlgebraicGeometry.Scheme.Hom

end
