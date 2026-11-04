module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseLocality
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDataReindex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent for affine morphisms along a quasi-compact fpqc covering

Let `f : X ⟶ S` be a surjective, flat, quasi-compact morphism of schemes, so that `{X ⟶ S}` is
an fpqc covering of `S` on its own, and let `(V, φ)` be a descent datum relative to `X/S` whose
structure morphism `V ⟶ X` is affine. Then `(V, φ)` is effective.

This is the one-member case of [Stacks, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
over an arbitrary base. It combines the reduction of effectivity to an affine base,
`AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_affineBaseCase`, with the affine
case itself, `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_affineBase`.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom`: a descent datum relative to a
  surjective flat quasi-compact morphism whose structure morphism is affine is effective.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentDatum

/-- **Effective descent for affine morphisms along a single quasi-compact fpqc covering.** A
descent datum relative to a surjective flat quasi-compact morphism `f : X ⟶ S` whose structure
morphism `V ⟶ X` is affine is effective: it is the canonical descent datum of a scheme over
`S`. -/
@[sga "1 VIII 7.8" "special case",
  sga "1 VIII 7.9" "special case",
  sga "3 IX 2.3" "partial",
  sga "3 VIII 1.7.2" "more general",
  sga "3 X 5.4" "special case",
  sga "3 XXIV 3.11.2" "partial"]
theorem isEffective_of_isAffineHom {S X : Scheme.{u}} {f : X ⟶ S}
    [Surjective f] [Flat f] [QuasiCompact f] (D : DescentDatum f)
    (haff : IsAffineHom D.over.hom) : DescentData.IsEffective D :=
  isEffective_of_isAffineHom_of_affineBaseCase
    (fun _ _ _ _ _ _ _ D' h' ↦ isEffective_of_isAffineHom_of_affineBase D' h') D haff

end AlgebraicGeometry.DescentDatum

end
