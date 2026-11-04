module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModelBundle

/-!
# Recognizing a local-model bundle from charts over affine opens

`Stacks.AffineBundle.IsLocalModelBundle` asks, at every point of the target, for an open
neighbourhood `V` of it, an isomorphism of `Spec B` with `V` and an isomorphism of the part of the
source lying over `V` with the spectrum of the local model `B[z₁, z₂]/(z₁z₂ - b)`, compatibly with
the restriction `f ∣_ V` of the morphism. In practice the open neighbourhood produced is an affine
open of the target and the ring `B` is its ring of sections, and the compatibility available is
not with `f ∣_ V` but with the composite `(f ⁻¹ᵁ V).ι ≫ f` — that is the shape in which
`Stacks.Divisors.zeroSchemeAffineOpenIso_comp` presents the identification of a zero scheme over
an affine open.

This file converts the second shape into the first.

## Main results

* `Stacks.AffineBundle.isLocalModelBundle_of_charts` — **a morphism admitting, locally on the
  target, a chart identifying it with the structure morphism of a local model over an affine open
  is a local-model bundle.**

## Implementation notes

The open immersion `V.ι` of an open subscheme is a monomorphism, so an equation between two
morphisms into `V` may be checked after composing with it; on the right-hand side
`AlgebraicGeometry.morphismRestrict_ι` turns `f ∣_ V ≫ V.ι` into `(f ⁻¹ᵁ V).ι ≫ f`, and on the
left `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι` turns `hV.isoSpec.inv ≫ V.ι` into
`hV.fromSpec`. No inverse has to be moved across the equation.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AffineBundle

/-- **A morphism that is, locally on the target, the structure morphism of a local model over an
affine open is a local-model bundle.** The compatibility hypothesis is stated for the composite
`(f ⁻¹ᵁ V).ι ≫ f` with the open immersion of `V`, rather than for the restriction `f ∣_ V`; the
two are interchangeable because `V.ι` is a monomorphism. -/
theorem isLocalModelBundle_of_charts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V) (_ : y ∈ V) (b : Γ(Y, V))
      (e : (f ⁻¹ᵁ V).toScheme ≅ Spec (CommRingCat.of (LocalModel Γ(Y, V) b))),
        e.hom ≫ localModelSpecMap Γ(Y, V) b ≫ hV.fromSpec = (f ⁻¹ᵁ V).ι ≫ f) :
    IsLocalModelBundle f := by
  intro y
  obtain ⟨V, hV, hyV, b, e, he⟩ := h y
  refine ⟨V, hyV, Γ(Y, V), inferInstance, b, e, hV.isoSpec.symm, ?_⟩
  rw [← cancel_mono V.ι, morphismRestrict_ι, Category.assoc, Category.assoc,
    Iso.symm_hom, IsAffineOpen.isoSpec_inv_ι]
  exact he

end Stacks.AffineBundle

end
