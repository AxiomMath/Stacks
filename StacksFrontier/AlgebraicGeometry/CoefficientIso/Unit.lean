module

public import StacksFrontier.AlgebraicGeometry.CoefficientIso.Basic

/-!
# The unit of `f^* ⊣ f_*` at an open immersion, on sections

The restriction maps of the coefficient system of [Stacks, Tag 01XL] are, by
`Stacks.AlgebraicGeometry.RelativeCechComplex.relativeCechRestriction_eq`, built from
`Stacks.AlgebraicGeometry.RelativeCechComplex.relativeUnit`, whose two ingredients are the unit
of `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` and the comparison
isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp`.  Neither has a section-level formula
in pinned Mathlib, and that is what blocks the naturality in the open set of
`Stacks.Tag01XLCoefficientIso.absoluteCechOpensPresheafEvalIso`.

This file supplies the first of the two, for an **open immersion**, which is the only case
[Stacks, Tag 01XL] uses: the unit of `f^* ⊣ f_*` is the unit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` — a single presheaf restriction map,
`Γ(M, U) ⟶ Γ(M, f ''ᵁ f ⁻¹ᵁ U)` — followed by the direct image of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

The mechanism is that `restrictFunctorIsoPullback` is *by definition*
`CategoryTheory.Adjunction.leftAdjointUniq` of the two adjunctions with the same right adjoint
`f_*`, so `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` applies verbatim.

## Main results

* `Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app`: the unit of `f^* ⊣ f_*`
  factored through the unit of `restrictAdjunction`.
* `Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app_app`: **the same on
  sections over an open set**, the first factor being an honest presheaf restriction map.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.Tag01XLCoefficientIso

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- **The unit of `f^* ⊣ f_*` at an open immersion is the unit of restriction**, followed by the
direct image of `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.  The two left
adjoints `restrictFunctor f` and `pullback f` share the right adjoint `f_*`, and
`restrictFunctorIsoPullback` is their `CategoryTheory.Adjunction.leftAdjointUniq`. -/
theorem unit_pullbackPushforwardAdjunction_app (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M =
      (Scheme.Modules.restrictAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) :=
  (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M).symm

/-- **The unit of `f^* ⊣ f_*` at an open immersion, on sections over an open set.**  Its first
factor is the restriction map `Γ(M, U) ⟶ Γ(M, f ''ᵁ f ⁻¹ᵁ U)` of the presheaf of `M`; the second
is the component of `restrictFunctorIsoPullback` over `f ⁻¹ᵁ U`. -/
theorem unit_pullbackPushforwardAdjunction_app_app (M : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U =
      M.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M).app (f ⁻¹ᵁ U) := by
  rw [unit_pullbackPushforwardAdjunction_app f M]
  rfl

end Stacks.Tag01XLCoefficientIso

end
