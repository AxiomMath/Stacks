module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.Defs
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay

/-!
# Gorenstein morphisms of algebraic spaces are Cohen–Macaulay

A morphism of algebraic spaces over a scheme `S` which is Gorenstein at a point of its source
(Tag 0E14) is Cohen–Macaulay there (Tag 0E0V). Hence a Gorenstein morphism of algebraic spaces
is a Cohen–Macaulay morphism. This is the space-level form of Tag 0C06, which the source uses in
this form in the proof of Tag 0E6M.

## Main results

* `AlgebraicGeometry.hasCohenMacaulayFiberLocalRing_of_hasGorensteinFiberLocalRing`: the
  germ-level fibre condition of Tag 0E13 implies that of Tag 0E0U.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_of_isGorensteinAt`: Gorenstein at a point implies
  Cohen–Macaulay at that point.
* `AlgebraicGeometry.Space.isCohenMacaulay_of_isGorenstein`: a Gorenstein morphism of algebraic
  spaces is Cohen–Macaulay.

## Implementation notes

Both `AlgebraicGeometry.Space.IsGorensteinAt` and `AlgebraicGeometry.Space.IsCohenMacaulayAt`
are flatness at the point together with a germ condition on every pointed étale chart, and the
two germ conditions concern the same local ring of the fibre, which carries its own
Noetherianity witness. So the flatness conjunct is shared and the germ conditions compare chart
by chart through the ring-level statement that a Gorenstein local ring is Cohen–Macaulay,
`Dualizing.IsGorensteinLocalRing.isCohenMacaulayLocalRing`. No standing hypothesis on the
morphism is needed.

## References

* [Stacks Project, Tag 0C06](https://stacks.math.columbia.edu/tag/0C06)
* [Stacks Project, Tag 0E14](https://stacks.math.columbia.edu/tag/0E14)
* [Stacks Project, Tag 0E0V](https://stacks.math.columbia.edu/tag/0E0V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The fibre local ring of a morphism of germs is Cohen–Macaulay when it is Noetherian and
Gorenstein: the germ condition of Tag 0E13 implies that of Tag 0E0U. -/
theorem hasCohenMacaulayFiberLocalRing_of_hasGorensteinFiberLocalRing
    {X S : GermOfScheme.{u}} {f : MorphismOfGerms X S} (h : HasGorensteinFiberLocalRing f) :
    HasCohenMacaulayFiberLocalRing f := by
  obtain ⟨g, hg, hN, hgor⟩ := h
  exact ⟨g, hg, hN, Dualizing.IsGorensteinLocalRing.isCohenMacaulayLocalRing _ hgor⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of algebraic spaces over `S` which is Gorenstein at a point of its source is
Cohen–Macaulay at that point: the space-level form of Tag 0C06. -/
theorem isCohenMacaulayAt_of_isGorensteinAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {x : points B S hS X} (h : IsGorensteinAt B S hS f x) :
    IsCohenMacaulayAt B S hS f x :=
  ⟨h.1, fun c => hasCohenMacaulayFiberLocalRing_of_hasGorensteinFiberLocalRing (h.2 c)⟩

/-- A Gorenstein morphism of algebraic spaces over `S` is Cohen–Macaulay: the space-level form
of Tag 0C06. -/
theorem isCohenMacaulay_of_isGorenstein {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} (h : IsGorenstein B S hS f) : IsCohenMacaulay B S hS f :=
  fun x => isCohenMacaulayAt_of_isGorensteinAt B S hS (h x)

end Space

end AlgebraicGeometry

end
