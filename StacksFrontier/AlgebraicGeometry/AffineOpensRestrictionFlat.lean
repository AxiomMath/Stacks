module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Restriction of functions between affine opens is flat

Let `X` be a scheme and let `V ≤ W` be affine opens of `X`. The restriction of functions
`Γ(X, W) → Γ(X, V)` is flat, and the morphism of spectra it induces is an open immersion.

## Main results

* `AlgebraicGeometry.IsAffineOpen.isOpenImmersion_Spec_map_presheaf_map`: the morphism of spectra
  induced by the restriction of functions between affine opens is an open immersion.
* `AlgebraicGeometry.IsAffineOpen.flat_presheaf_map`: **the restriction of functions between affine
  opens is flat**, as a `RingHom.Flat`.
* `AlgebraicGeometry.IsAffineOpen.moduleFlat_presheaf_map`: the same, as a `Module.Flat` for the
  algebra structure the restriction defines.

## Implementation notes

`RingHom.Flat f` unfolds to `Module.Flat R S` for the module structure `f` defines, so the two
forms of flatness above differ only in the spelling of the instance.

## References

* [Stacks Project, Lemma 26.11.14 (Tag 01SN)](https://stacks.math.columbia.edu/tag/01SN)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} {V W : X.Opens}

/-- The morphism of spectra induced by the restriction of functions from an affine open `W` to an
affine open `V ≤ W` is an open immersion. -/
theorem isOpenImmersion_Spec_map_presheaf_map (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h : V ≤ W) : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h : V ⟶ W).op)) := by
  have key : Spec.map (X.presheaf.map (homOfLE h : V ⟶ W).op) ≫ hW.fromSpec = hV.fromSpec :=
    hW.map_fromSpec hV (homOfLE h).op
  have : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h : V ⟶ W).op) ≫ hW.fromSpec) := by
    rw [key]; infer_instance
  exact IsOpenImmersion.of_comp _ hW.fromSpec

/-- **The restriction of functions from an affine open to a smaller affine open is flat.** -/
theorem flat_presheaf_map (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W) :
    RingHom.Flat (X.presheaf.map (homOfLE h : V ⟶ W).op).hom := by
  have hoi := hV.isOpenImmersion_Spec_map_presheaf_map hW h
  have hfl : AlgebraicGeometry.Flat (Spec.map (X.presheaf.map (homOfLE h : V ⟶ W).op)) :=
    inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)).mp hfl

/-- `AlgebraicGeometry.IsAffineOpen.flat_presheaf_map` in the `Module.Flat` spelling, for the
algebra structure the restriction of functions defines. -/
theorem moduleFlat_presheaf_map (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W) :
    letI : Algebra Γ(X, W) Γ(X, V) := (X.presheaf.map (homOfLE h : V ⟶ W).op).hom.toAlgebra
    Module.Flat Γ(X, W) Γ(X, V) :=
  hV.flat_presheaf_map hW h

end AlgebraicGeometry.IsAffineOpen

end
