module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint

/-!
# Smoothness at a point read on the stalk, and the flatness half of condition (2)

Condition (2) of Stacks Tag 01V9 is a conjunction: the map of local rings induced by `f` at `x`
is flat, and the scheme-theoretic fibre through `x` is smooth at `x`.  **This file proves the
first conjunct from condition (1)**, and records the reduction of condition (1) itself to a
property of the induced map of local rings.

## Main results

* `Stacks.SmoothAtJacobian.condition1_imp_flat_stalkMap`: if `f` is smooth at `x` then the
  induced map of local rings at `x` is flat.  This is the first conjunct of each of conditions
  (2), (3) and (4).
* `Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus`: for `f` locally of finite
  presentation, smoothness at `x` is membership of `x` in the smooth locus, that is, formal
  smoothness of the induced map of local rings.

## Implementation notes

Flatness of the induced map of local rings comes from flatness of the morphism, which Mathlib
derives from smoothness, together with the identification
`AlgebraicGeometry.Scheme.Hom.resLEStalkMap` of the stalk map of a restricted morphism with the
stalk map of the morphism.  Flatness of a ring map is invariant under isomorphism of arrows, so
that identification transports it; no finiteness hypothesis on `f` is used.

The second statement is the two halves of Mathlib's `Scheme.Hom.smoothLocus` fitted together.
Its forward direction is `InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap`, and its reverse
direction is `AlgebraicGeometry.exists_smooth_of_formallySmooth_stalk` followed by
`InfinitesimalLifting.smoothAt_iff_exists_affine`.  It assumes only that `f` is locally of finite
presentation, which Tag 01V9 assumes throughout, and so is weaker in hypotheses than
`InfinitesimalLifting.formallySmooth_stalkMap_smoothAt`, which needs a locally Noetherian base
and only local finiteness of type.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.SmoothAtJacobian

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- **Condition (1) of Tag 01V9 implies the flatness conjunct of conditions (2), (3) and (4).**
If `f` is smooth at `x` then the induced map of local rings at `x` is flat. -/
public theorem condition1_imp_flat_stalkMap (h : Condition1 f x) : (f.stalkMap x).hom.Flat := by
  obtain ⟨U, hxU, hsmooth⟩ := h
  have hg := AlgebraicGeometry.Flat.stalkMap (f.resLE ⊤ U le_top) ⟨x, hxU⟩
  rwa [RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (Scheme.Hom.resLEStalkMap f (le_top : U ≤ f ⁻¹ᵁ ⊤) ⟨x, hxU⟩)] at hg

/-- **Condition (1) of Tag 01V9 is a condition on the induced map of local rings.** For a
morphism locally of finite presentation, smoothness at a point is formal smoothness of the
induced map of local rings there, that is, membership of the point in the smooth locus. -/
public theorem condition1_iff_mem_smoothLocus [LocallyOfFinitePresentation f] :
    Condition1 f x ↔ x ∈ f.smoothLocus := by
  refine ⟨fun h => Scheme.Hom.mem_smoothLocus.mpr (h.formallySmooth_stalkMap f x), fun hx => ?_⟩
  obtain ⟨V, hV, U, hU, hUV, hxU, H⟩ :=
    exists_smooth_of_formallySmooth_stalk f x (Scheme.Hom.mem_smoothLocus.mp hx)
  exact (InfinitesimalLifting.smoothAt_iff_exists_affine f x).2 ⟨U, V, hU, hV, hxU, hUV, H⟩

end Stacks.SmoothAtJacobian

end
