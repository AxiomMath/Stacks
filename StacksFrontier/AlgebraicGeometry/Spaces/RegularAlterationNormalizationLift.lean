module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteRegularAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# A regular alteration factors through the normalization

Let `f : X ⟶ Y` be an alteration of an integral algebraic space `Y` over `S` with `X` regular,
and let `ν : Y^ν ⟶ Y` be a normalization of `Y`. Then `f` factors uniquely as `g ≫ ν`, and the
factor `g : X ⟶ Y^ν` is proper.

## Main results

* `AlgebraicGeometry.Space.NormalizationData.existsUnique_lift_of_isAlteration`: the unique
  factorization through the normalization.
* `AlgebraicGeometry.Space.NormalizationData.isProper_lift`: the factor through the
  normalization of a proper morphism is proper.

## Implementation notes

The factorization is part (4) of Stacks 0BB4: `X` is normal because it is regular (Stacks 0BGT),
and `f` carries points of codimension zero to points of codimension zero because it is a
dominant morphism of integral algebraic spaces. Properness of the factor is Stacks 04NX, part
(2), the normalization morphism being integral, hence separated.

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

namespace NormalizationData

/-- A regular alteration of an integral algebraic space factors uniquely through its
normalization. -/
theorem existsUnique_lift_of_isAlteration (D : NormalizationData B S hS Y) (f : X ⟶ Y)
    (hf : IsAlteration B S hS f)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T)) :
    ∃! g : X ⟶ D.space, g ≫ D.hom = f :=
  D.existsUnique_lift_hom hf.1 hf.2.2.1 (isNormal_of_isRegular B S hS X hXreg) f
    (localRingDimension_eq_zero_of_isDominant_of_isIntegralSpace B S hS hf.2.2.1 hf.1
      hf.2.2.2.1 hf.2.1 f hf.isDominant)

/-- The factor through the normalization of a proper morphism is proper. -/
theorem isProper_lift (D : NormalizationData B S hS Y) (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y} (hf : IsProper B S hS f) (g : X ⟶ D.space)
    (hg : g ≫ D.hom = f) : IsProper B S hS g :=
  isProper_of_comp_of_isSeparated B S hS hX D.isAlgebraicSpace hY g D.hom (hg ▸ hf)
    (isSeparated_of_isIntegralHom B S hS D.hom D.isAlgebraicSpace hY (D.isIntegralHom_hom hY))

end NormalizationData

end AlgebraicGeometry.Space

end
