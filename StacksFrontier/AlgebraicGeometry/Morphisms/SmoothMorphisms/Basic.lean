module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksCore.Tactic.StacksAttribute

/-!
# Smooth morphisms of schemes are syntomic

A smooth morphism of schemes is syntomic: around every point of the source one finds affine
opens on which the morphism is given by a smooth ring map, and a smooth ring map is syntomic.

The base change of a smooth morphism is smooth ([Stacks, Tag 01VB]); this is Mathlib's
`AlgebraicGeometry.smooth_isStableUnderBaseChange`, registered here.

## Main results

* `AlgebraicGeometry.syntomic_of_smooth` states that every smooth morphism of schemes is
  syntomic.

## Implementation notes

Smoothness is Mathlib's `AlgebraicGeometry.Smooth` class, and syntomicity is the pointwise
predicate `AlgebraicGeometry.Syntomic`. The proof chooses an affine open of the target
containing the image of the point and an affine open of the source inside its preimage, then
transfers smoothness of the induced ring map to syntomicity.

## References

* [Stacks Project, Tag 01VB](https://stacks.math.columbia.edu/tag/01VB)
* [Stacks Project, Tag 01VD](https://stacks.math.columbia.edu/tag/01VD)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A smooth morphism of schemes is syntomic. -/
@[stacks 01VD]
theorem syntomic_of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] : Syntomic f := by
  intro x
  obtain ⟨V, hV, hfxV, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (Opens.mem_top (f x))
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ f ⁻¹ᵁ V from hfxV)
  refine ⟨⟨U, hU⟩, hxU, ⟨V, hV⟩, hUV, ?_⟩
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  exact (f.smooth_appLE hV hU hUV).toAlgebra.syntomic _ _

end AlgebraicGeometry

add_to_stacks 01VB "the base change of a smooth morphism is smooth"
  AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_sga "1 II 1.3" "more general" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_sga "1 II 4.13" "global ascent" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "smooth morphisms" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_sga "3 VIB 2.1.2" "partial" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_sga "3 XIX 2.1" "(i)" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_sga "6 VIII 1.6" "partial" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_sga "6 VIII 1.8" "partial" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_sga "6 X 7.13.3" "partial" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_ega "IV 17.3.3" "smooth branch of (iii)" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_ega "IV 17.7.3" "(ii)" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_ega "IV 6.8.2" "globally smooth f" AlgebraicGeometry.smooth_isStableUnderBaseChange
add_to_ega "IV 6.8.3" "more general" AlgebraicGeometry.smooth_isStableUnderBaseChange
