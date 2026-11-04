module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic fibre of a dominant morphism from an irreducible scheme is irreducible

Let `f : X → Y` be a dominant morphism of schemes with `X` irreducible, and let `η` be the
generic point of `Y`. Then the generic fibre `X_η = X ×_Y Spec κ(η)` is irreducible.

The reason is purely topological: the generic point `ξ` of `X` maps to a point whose closure is
all of `Y`, so it maps to `η`; the fibre of `f` over `η` therefore *contains* `ξ`, and any subset
of a space containing a point whose closure is the whole space is irreducible. The passage from
the subset `f⁻¹(η)` of `X` to the scheme-theoretic fibre is Mathlib's
`AlgebraicGeometry.Scheme.Hom.fiberHomeo`.

This is the input that the generic-fibre stage of a Bertini-type argument needs: irreducibility
of `X_η` as a scheme, so that `X_η` has a generic point and hence a function field, to which
[Stacks, Tag 054Q] can then be applied. Irreducibility of `X` alone is *not* that statement —
it is this lemma's hypothesis.

## Main results

* `isIrreducible_of_mem_of_isGenericPoint`: a subset of a space containing a point whose closure
  is the whole space is irreducible.
* `AlgebraicGeometry.Scheme.Hom.irreducibleSpace_fiber_of_genericPoint`: the fibre of `f` over
  the image of the generic point of an irreducible `X` is irreducible.
* `AlgebraicGeometry.Scheme.Hom.base_genericPoint_eq_of_denseRange`: a dominant morphism from an
  irreducible scheme carries the generic point to a generic point.
* `AlgebraicGeometry.Scheme.Hom.irreducibleSpace_fiber_of_denseRange`: **the generic fibre of a
  dominant morphism from an irreducible scheme is irreducible.**

## Implementation notes

Dominance is spelled `DenseRange f.base` rather than through a morphism property, and the
generic point of the target is given as a point `η` with `IsGenericPoint η Set.univ` rather than
as `genericPoint Y`, because that is the shape in which the Bertini argument has it — the
parameter space is presented as an affine space and its generic point comes from the polynomial
ring. The scheme-theoretic fibre is Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber`, so the
statement is directly about `f.fiberToSpecResidueField η`'s source.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

/-- **A set containing a dense point is irreducible.** If the closure of `{x}` is the whole
space, then every subset of the space containing `x` is irreducible: two opens meeting the subset
meet `{x}`, hence both contain `x`. -/
theorem isIrreducible_of_mem_of_isGenericPoint {α : Type*} [TopologicalSpace α] {x : α}
    (hx : IsGenericPoint x Set.univ) {s : Set α} (hxs : x ∈ s) : IsIrreducible s := by
  refine ⟨⟨x, hxs⟩, fun u v hu hv hsu hsv => ?_⟩
  obtain ⟨a, -, hau⟩ := hsu
  obtain ⟨b, -, hbv⟩ := hsv
  exact ⟨x, hxs, (hx.mem_open_set_iff hu).mpr ⟨a, trivial, hau⟩,
    (hx.mem_open_set_iff hv).mpr ⟨b, trivial, hbv⟩⟩

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The fibre through the generic point of an irreducible scheme is irreducible.** If `X` is
irreducible and its generic point lies over `y`, then the scheme-theoretic fibre `X_y` is
irreducible: as a subspace of `X` it contains the generic point of `X`, whose closure is all of
`X`. -/
@[ega "0 2.1.8" "special case"]
theorem irreducibleSpace_fiber_of_genericPoint [IrreducibleSpace X] {y : Y}
    (hy : f.base (genericPoint X) = y) : IrreducibleSpace (f.fiber y) :=
  have := Subtype.irreducibleSpace
    (isIrreducible_of_mem_of_isGenericPoint (genericPoint_spec X) (s := f.base ⁻¹' {y}) hy)
  (f.fiberHomeo y).irreducibleSpace_iff.mpr inferInstance

/-- **A dominant morphism from an irreducible scheme carries the generic point to the generic
point.** The closure of the image of the generic point is the closure of the image of `X`, which
is all of `Y`; and a scheme is `T₀`, so a generic point is unique. -/
@[ega "I 6.5.5" "partial"]
theorem base_genericPoint_eq_of_denseRange [IrreducibleSpace X] (hf : DenseRange f.base) {η : Y}
    (hη : IsGenericPoint η Set.univ) : f.base (genericPoint X) = η := by
  have h : IsGenericPoint (f.base (genericPoint X)) Set.univ := by
    have himg := (genericPoint_spec X).image (f := f.base) f.continuous
    rwa [Set.image_univ, hf.closure_range] at himg
  exact h.eq hη

/-- **The generic fibre of a dominant morphism from an irreducible scheme is irreducible.** -/
theorem irreducibleSpace_fiber_of_denseRange [IrreducibleSpace X] (hf : DenseRange f.base)
    {η : Y} (hη : IsGenericPoint η Set.univ) : IrreducibleSpace (f.fiber η) :=
  f.irreducibleSpace_fiber_of_genericPoint (f.base_genericPoint_eq_of_denseRange hf hη)

end AlgebraicGeometry.Scheme.Hom

end
