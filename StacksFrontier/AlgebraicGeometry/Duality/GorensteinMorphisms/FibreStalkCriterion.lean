module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Basic

/-!
# Gorenstein points of a flat morphism and the local rings of its fibres

A morphism of schemes with locally Noetherian fibres which is flat is Gorenstein at a point of
its source exactly when the local ring of its fibre through that point is Gorenstein. This is
the first link in the chain of equivalences of [Stacks, Tag 0C08], and the one where flatness
is used.

## Main definitions

* `Stacks.Duality.IsGorensteinFiberStalkAt` — the local ring of the fibre of a morphism
  through a point of its source is Gorenstein.

## Main results

* `Stacks.Duality.isGorensteinAt_iff_isGorensteinFiberStalkAt` — for a flat morphism, being
  Gorenstein at a point is Gorensteinness of that fibre local ring.

## References

* [Stacks Project, Tag 0C08](https://stacks.math.columbia.edu/tag/0C08)
* [Stacks Project, Tag 0C04](https://stacks.math.columbia.edu/tag/0C04)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}}

/-- A morphism with locally Noetherian fibres has Gorenstein fibre stalk at `x` when the local
ring of its fibre over `f x` at the canonical point `f.asFiber x` is Gorenstein. This is
condition (2) in the chain of equivalences proving [Stacks, Tag 0C08]. -/
abbrev IsGorensteinFiberStalkAt (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x : X) : Prop :=
  letI := hf (f x)
  Dualizing.IsGorensteinLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))

/-- **Stacks Project, Tag 0C08**, the first equivalence of its proof. A flat morphism with
locally Noetherian fibres is Gorenstein at a point exactly when the local ring of its fibre
through that point is Gorenstein. -/
@[stacks 0C08 "proof chain (1) ↔ (2); (2)↔…↔(6) needs 0A9Y, 0BZZ, 0BFQ invertibility"]
theorem isGorensteinAt_iff_isGorensteinFiberStalkAt (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) [Flat f] (x : X) :
    f.IsGorensteinAt hf x ↔ IsGorensteinFiberStalkAt f hf x :=
  ⟨fun h => h.2, fun h => ⟨AlgebraicGeometry.Flat.stalkMap f x, h⟩⟩

end Stacks.Duality
