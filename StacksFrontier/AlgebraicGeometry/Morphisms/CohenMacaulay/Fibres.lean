module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohen–Macaulay morphisms and their fibres

For a morphism of schemes with locally Noetherian fibres, being Cohen–Macaulay is equivalent to
being flat with Cohen–Macaulay fibres.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_iff_flat_and_fibers` characterizes Cohen–Macaulay
  morphisms by flatness and Cohen–Macaulayness of every fibre.

## Implementation notes

The locally Noetherian fibre hypothesis is passed explicitly to the definition of a
Cohen–Macaulay morphism. Flatness uses Mathlib's predicate for scheme morphisms, while
Cohen–Macaulayness of each fibre uses the scheme predicate
`AlgebraicGeometry.IsCohenMacaulay`.

## References

* [Stacks Project, Tag 045S](https://stacks.math.columbia.edu/tag/045S)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- At a point of a fibre which comes from a point of the source, Cohen–Macaulayness of the
morphism gives Cohen–Macaulayness of the fibre local ring. -/
private theorem fiberPoint_isCohenMacaulay
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (h : Scheme.Hom.IsCohenMacaulay f hf) {x : X} {y : Y}
    (hxy : f x = y) (z : f.fiber y) (hz : f.fiberι y z = x) :
    ∃ hN : IsNoetherianRing ((f.fiber y).presheaf.stalk z),
      @IsCohenMacaulayLocalRing ((f.fiber y).presheaf.stalk z) _ hN _ := by
  cases hxy
  have hza : z = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (by simpa using hz)
  rw [hza]
  let _ := hf (f x)
  exact ⟨inferInstance, (h x).2⟩

/-- A morphism with locally Noetherian fibres is Cohen–Macaulay precisely when it is flat and
every fibre is a Cohen–Macaulay scheme. -/
@[stacks 045S, ega "IV 19.2.9" "more general"]
public theorem isCohenMacaulay_iff_flat_and_fibers {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) :
    Scheme.Hom.IsCohenMacaulay f hf ↔
      Flat f ∧ (∀ y : Y, IsCohenMacaulay (f.fiber y)) := by
  refine ⟨fun h => ⟨(Flat.iff_flat_stalkMap f).2 fun x => (h x).1, fun y =>
    ((isCohenMacaulay_tfae_stalk (f.fiber y)).out 1 2 rfl rfl).mpr
      ⟨hf y, fun z => fiberPoint_isCohenMacaulay f hf h (f.fiberHomeo y z).property z rfl⟩⟩,
    fun ⟨hflat, hfib⟩ x => ⟨(Flat.iff_flat_stalkMap f).mp hflat x, ?_⟩⟩
  let _ := hf (f x)
  obtain ⟨hN, hCM⟩ :=
    (((isCohenMacaulay_tfae_stalk (f.fiber (f x))).out 1 2 rfl rfl).mp
      (hfib (f x))).2 (f.asFiber x)
  let _ : IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := hN
  exact hCM

end AlgebraicGeometry
