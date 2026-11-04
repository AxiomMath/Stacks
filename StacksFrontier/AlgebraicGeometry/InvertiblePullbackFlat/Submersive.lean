module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import StacksCore.Tactic.StacksAttribute

/-!
# Flat morphisms with nonempty fibres are submersive

A morphism of schemes with nonempty fibres is surjective, because the scheme-theoretic fibre
`f.fiber y` has `f ⁻¹' {y}` as the range of `f.fiberι y`.

For a flat morphism the resulting surjection is a quotient map on underlying spaces under
either of two finiteness hypotheses: quasi-compactness, where this is Stacks Tag 02JY, or
local finiteness of type over a locally Noetherian base, where the morphism is even open
(Stacks Tag 01UA, after upgrading finite type to finite presentation). This disjunction is
hypothesis (4) of Stacks Tag 0BD7, and the last paragraph of its proof is exactly the
statement that a subset of the base whose preimage is closed is closed.

## Main results

* `AlgebraicGeometry.Surjective.of_nonempty_fiber`: a morphism with nonempty fibres is
  surjective.
* `AlgebraicGeometry.isQuotientMap_of_flat_of_nonempty_fiber`: a flat morphism with nonempty
  fibres which is quasi-compact, or locally of finite type over a locally Noetherian base, is
  a quotient map.
* `AlgebraicGeometry.isClosed_of_isClosed_preimage_of_flat`: the consequence used in Tag 0BD7,
  that such a morphism detects closed subsets of the base.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02JY](https://stacks.math.columbia.edu/tag/02JY)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes all of whose scheme-theoretic fibres are nonempty is surjective. -/
theorem Surjective.of_nonempty_fiber (hfiber : ∀ y : Y, Nonempty (f.fiber y)) :
    Surjective f where
  surj y := by
    obtain ⟨x⟩ := hfiber y
    have hx : (f.fiberι y) x ∈ Set.range (f.fiberι y) := Set.mem_range_self x
    rw [f.range_fiberι y] at hx
    exact ⟨f.fiberι y x, hx⟩

/-- A flat morphism with nonempty fibres, quasi-compact or locally of finite type over a
locally Noetherian base, is a quotient map on underlying topological spaces.

For the quasi-compact case this is Stacks Tag 02JY; in the finite type case the morphism is
locally of finite presentation, hence open by Stacks Tag 01UA. -/
@[ega "II 8.11.1" "special case", ega "IV 15.7.8" "partial"]
theorem isQuotientMap_of_flat_of_nonempty_fiber [IsLocallyNoetherian Y] [Flat f]
    (hfiber : ∀ y : Y, Nonempty (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f) :
    Topology.IsQuotientMap f := by
  have hsurj : Surjective f := .of_nonempty_fiber f hfiber
  obtain hqc | hft := hfinite
  · exact Flat.isQuotientMap_of_surjective f
  · have : LocallyOfFinitePresentation f :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr hft
    exact IsOpenMap.isQuotientMap f.isOpenMap f.continuous f.surjective

/-- The last step of the proof of Stacks Tag 0BD7: for a flat morphism with nonempty fibres
which is quasi-compact or locally of finite type over a locally Noetherian base, a subset of
the base is closed as soon as its preimage is closed. -/
theorem isClosed_of_isClosed_preimage_of_flat [IsLocallyNoetherian Y] [Flat f]
    (hfiber : ∀ y : Y, Nonempty (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f)
    {T : Set Y} (hT : IsClosed (f ⁻¹' T)) : IsClosed T :=
  (isQuotientMap_of_flat_of_nonempty_fiber f hfiber hfinite).isCoinducing.isClosed_preimage.mp hT

/-- The open variant of `isClosed_of_isClosed_preimage_of_flat`. -/
theorem isOpen_of_isOpen_preimage_of_flat [IsLocallyNoetherian Y] [Flat f]
    (hfiber : ∀ y : Y, Nonempty (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f)
    {T : Set Y} (hT : IsOpen (f ⁻¹' T)) : IsOpen T :=
  (isQuotientMap_of_flat_of_nonempty_fiber f hfiber hfinite).isCoinducing.isOpen_preimage.mp hT

end AlgebraicGeometry
