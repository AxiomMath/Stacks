module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic

/-!
# Gorenstein morphisms are the flat morphisms with Gorenstein fibres

A morphism of schemes whose fibres are all locally Noetherian is a Gorenstein morphism exactly
when it is flat and every one of its fibres is a Gorenstein scheme.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber` is the
  equivalence.
* `AlgebraicGeometry.Scheme.Hom.isGorenstein_fiber_of_isGorenstein` and
  `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_of_flat_of_isGorenstein_fiber` are its two
  halves, the second stated pointwise on the source.

## References

* [Stacks Project, Tag 0C05](https://stacks.math.columbia.edu/tag/0C05)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A point of the fibre over `y` is the image of a point of the source lying over `y`, and
agrees with the canonical fibre point of that source point. -/
private lemma exists_asFiber_eq (y : Y) (p : f.fiber y) :
    ∃ x : X, ∃ h : f x = y, h ▸ f.asFiber x = p := by
  rcases hpt : f.fiberHomeo y p with ⟨x, hxy⟩
  have hfy : f x = y := by simpa using hxy
  have hxEq : x = f.fiberι y p :=
    (congrArg (fun q : f ⁻¹' {y} => (q : X)) hpt).symm.trans (Scheme.Hom.fiberHomeo_apply f y p)
  refine ⟨x, hfy, ?_⟩
  cases hfy
  apply (f.fiberι (f x)).isEmbedding.injective
  rw [Scheme.Hom.fiberι_asFiber]
  simp [hxEq]

/-- Every fibre of a Gorenstein morphism is a Gorenstein scheme. -/
public theorem isGorenstein_fiber_of_isGorenstein
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (h : IsGorenstein f hf) (y : Y) :
    AlgebraicGeometry.IsGorenstein (f.fiber y) := by
  refine { toIsLocallyNoetherian := hf y, isGorensteinLocalRing := fun p => ?_ }
  obtain ⟨x, hfy, hp⟩ := exists_asFiber_eq f y p
  cases hfy
  exact hp ▸ (h x).2

/-- A flat morphism all of whose fibres are Gorenstein schemes is Gorenstein at every point of
its source. -/
public theorem isGorensteinAt_of_flat_of_isGorenstein_fiber
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) [Flat f]
    (hG : ∀ y : Y, AlgebraicGeometry.IsGorenstein (f.fiber y)) (x : X) :
    IsGorensteinAt f hf x :=
  ⟨AlgebraicGeometry.Flat.stalkMap f x, (hG (f x)).isGorensteinLocalRing (f.asFiber x)⟩

/-- A morphism of schemes with locally Noetherian fibres is Gorenstein if and only if it is flat
and all of its fibres are Gorenstein schemes. -/
@[stacks 0C05]
public theorem isGorenstein_iff_flat_and_isGorenstein_fiber
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) :
    IsGorenstein f hf ↔ Flat f ∧ ∀ y : Y, AlgebraicGeometry.IsGorenstein (f.fiber y) :=
  ⟨fun h => ⟨AlgebraicGeometry.Flat.of_stalkMap f fun x => (h x).1,
      isGorenstein_fiber_of_isGorenstein f hf h⟩,
    fun ⟨_, hG⟩ => isGorensteinAt_of_flat_of_isGorenstein_fiber f hf hG⟩

end AlgebraicGeometry.Scheme.Hom
