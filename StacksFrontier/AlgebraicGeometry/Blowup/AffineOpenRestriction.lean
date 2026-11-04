module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProjGluing

/-!
# The restriction map between two affine opens

Let `U ≤ V` be affine opens of a scheme `S`. The restriction map `Γ(S, V) ⟶ Γ(S, U)` of the
structure sheaf presents `U` as an affine open subscheme of `V`, so `Spec` of it is an open
immersion and in particular it is a flat ring homomorphism. Both statements are consequences of
facts Mathlib already has, but neither is stated there for the restriction map itself.

Flatness is what makes the Rees algebra of a quasi-coherent ideal sheaf compatible with
restriction: the degree-`n` piece of the Rees algebra over `U` is `ℐ(U)ⁿ`, and the comparison
`Γ(S, U) ⊗_{Γ(S, V)} ℐ(V)ⁿ ⟶ ℐ(U)ⁿ` is injective precisely because `Γ(S, U)` is flat over
`Γ(S, V)`.

## Main results

* `AlgebraicGeometry.Scheme.isOpenImmersion_Spec_map_presheaf_map`: `Spec` of the restriction map
  between two affine opens is an open immersion.
* `AlgebraicGeometry.Scheme.flat_presheaf_map_of_isAffineOpen`: the restriction map between two
  affine opens is flat.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {U V : S.Opens}

/-- **`Spec` of the restriction map between two affine opens is an open immersion.** The square
`Stacks.RelativeProj.isoSpec_inv_homOfLE` identifies that morphism, up to the affine
identifications of `U` and `V`, with the inclusion `U ⟶ V` of open subschemes. -/
theorem isOpenImmersion_Spec_map_presheaf_map (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) : IsOpenImmersion (Spec.map (S.presheaf.map (homOfLE h).op)) := by
  have hcomp : IsOpenImmersion
      (Spec.map (S.presheaf.map (homOfLE h).op) ≫ hV.isoSpec.inv) := by
    rw [← Stacks.RelativeProj.isoSpec_inv_homOfLE hU hV h]
    infer_instance
  rwa [MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion)] at hcomp

/-- **The restriction map between two affine opens is flat.** An open immersion is flat, and
`Spec` of the restriction map is an open immersion. -/
theorem flat_presheaf_map_of_isAffineOpen (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) : (S.presheaf.map (homOfLE h).op).hom.Flat := by
  have := isOpenImmersion_Spec_map_presheaf_map hU hV h
  exact HasRingHomProperty.Spec_iff (P := @Flat).mp inferInstance

end AlgebraicGeometry.Scheme

end
