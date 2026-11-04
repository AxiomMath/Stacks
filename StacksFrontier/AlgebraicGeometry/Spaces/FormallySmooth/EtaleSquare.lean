module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Formal smoothness in a square with étale vertical arrows

In a commuting square of algebraic spaces over a scheme whose two vertical arrows are étale,
formal smoothness of the bottom arrow passes to the top arrow.

## Main results

* `AlgebraicGeometry.Space.formallySmooth_of_isEtale_square`: **Stacks 061H**.

## Implementation notes

An étale morphism of algebraic spaces is unramified by Tag 06CR and flat by Tag 0467, hence
formally étale by Tag 0615. So both vertical arrows are formally étale. The top arrow composed
with the right vertical arrow equals the left vertical arrow composed with the bottom arrow,
which is formally smooth as a composite of a formally étale and a formally smooth
transformation by Tag 049T; and the right vertical arrow is formally unramified, so Tag 04G5
cancels it.

The special case in which the four spaces of the square are a square of *scheme* charts of the
bottom arrow — which is what the proof of Tag 04AM consumes — is
`AlgebraicGeometry.Space.exists_lift_of_formallySmooth` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothFormallySmooth.lean`; it is proved there directly
from representability of the charts, without Tag 0615.

## References

* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 049T](https://stacks.math.columbia.edu/tag/049T)
* [Stacks Project, Tag 04G5](https://stacks.math.columbia.edu/tag/04G5)
* [Stacks Project, Tag 0615](https://stacks.math.columbia.edu/tag/0615)
* [Stacks Project, Tag 061H](https://stacks.math.columbia.edu/tag/061H)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 061H.** Let `ψ : U ⟶ V`, `u : U ⟶ X`, `v : V ⟶ Y` and `f : X ⟶ Y` be morphisms of
algebraic spaces over `S` forming a commuting square. If the two vertical arrows `u` and `v`
are étale and `f` is formally smooth, then `ψ` is formally smooth. -/
@[stacks 061H]
theorem formallySmooth_of_isEtale_square
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (ψ : U ⟶ V) (u : U ⟶ X) (v : V ⟶ Y) (f : X ⟶ Y)
    (hsq : u ≫ f = ψ ≫ v)
    (hu : IsEtale B S hS u) (hv : IsEtale B S hS v)
    (hf : FormallySmooth f) :
    FormallySmooth ψ := by
  have eu : FormallyEtale u := formallyEtale_of_isUnramified_of_isFlat B S hS hU hX u
    (isUnramified_of_isEtale B S hS hu) (isFlat_of_isEtale B S hS hu)
  have ev : FormallyEtale v := formallyEtale_of_isUnramified_of_isFlat B S hS hV hY v
    (isUnramified_of_isEtale B S hS hv) (isFlat_of_isEtale B S hS hv)
  refine formallySmooth_of_comp_of_formallyUnramified ψ v
    (fun T T' hT hT' i hi x y hxy z₁ z₂ hz₁ hz₂ =>
      (ev T T' hT hT' i hi x y hxy).unique hz₁ hz₂) ?_
  rw [← hsq]
  exact FormallySmooth.comp u f
    (fun T T' hT hT' i hi x y hxy => (eu T T' hT hT' i hi x y hxy).exists) hf

end AlgebraicGeometry.Space

end
