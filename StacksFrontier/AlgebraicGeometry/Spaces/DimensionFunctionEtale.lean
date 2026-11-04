module

public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# The induced dimension value is read off any étale cover of the source

Let `δ` be an integer-valued function on the points of an algebraic space `Y`, and let
`f : X ⟶ Y` be locally of finite type. The function induced on the points of `X` is the value
of `δ` at the image point plus the relative transcendence degree there. Precomposing `f` with
an étale morphism `g : X' ⟶ X` does not change that function: it is the value induced by `f`
at the image point.

This is the reason the induced function can be computed on an étale cover of its source. An
étale morphism is locally quasi-finite, so it contributes a finite residue-field extension and
hence no transcendence degree, and the image point of `z` under `g ≫ f` is the image under `f`
of the image of `z` under `g`.

## Main results

* `AlgebraicGeometry.Space.inducedDimensionValue_comp_of_isEtale`: the function induced by a
  morphism locally of finite type is constant along an étale morphism into its source, in the
  sense that precomposition reads it at the image point.

## References

* [Stacks Project, Tag 06RX](https://stacks.math.columbia.edu/tag/06RX)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- The value induced by a morphism `f` locally of finite type at the image of a point `z`
under an étale morphism `g` into its source is the value induced by `g ≫ f` at `z` itself.

An étale morphism is locally quasi-finite by Stacks 03XU, so the transcendence degree of `z`
over its image under `g ≫ f` is that of the image of `z` under `g` over the same point, by
Stacks 06RX; the two induced values therefore have the same transcendence-degree summand, and
the same base value because the two image points agree. -/
theorem inducedDimensionValue_comp_of_isEtale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X' X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (δ : points B S hS Y → ℤ) (g : X' ⟶ X)
    (hg : IsEtale B S hS g) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (z : points B S hS X') :
    inducedDimensionValue B S hS δ (g ≫ f) z =
      inducedDimensionValue B S hS δ f (pointsMap B S hS X' g z) := by
  obtain ⟨n, hn⟩ :=
    exists_finite_transcendenceDegreeAt B S hS f hf (pointsMap B S hS X' g z)
  have hcomp : HasTranscendenceDegreeAt B S hS (g ≫ f) z (n : ℕ∞) :=
    (hasTranscendenceDegreeAt_comp_iff_of_isLocallyQuasiFinite B S hS hX' hX hY g f
      (isLocallyQuasiFinite_of_isEtale B S hS hX hg) z (n : ℕ∞)).mpr hn
  rw [inducedDimensionValue_eq B S hS hX' hY δ (g ≫ f)
      (isLocallyOfFiniteType_comp B S hS hX' hX hY g f
        (isLocallyOfFiniteType_of_isEtale B S hS hX hg) hf) z (n : ℕ∞) hcomp,
    inducedDimensionValue_eq B S hS hX hY δ f hf (pointsMap B S hS X' g z) (n : ℕ∞) hn,
    pointsMap_comp_apply]

end AlgebraicGeometry.Space

end
