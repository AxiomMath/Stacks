module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Finiteness of the relative spectrum of an algebra sheaf

An algebra sheaf on a scheme `S` is *finite*, resp. *of finite presentation*, when its structural
ring map is module-finite, resp. of finite presentation, on the sections over every affine open.
This file shows that these two conditions are inherited by the structure morphism of the relative
spectrum: the relative spectrum of a finite quasi-coherent algebra sheaf is finite over the base,
and the relative spectrum of a finite and finitely presented one is of finite presentation over
the base.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.IsFinite` and
  `Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation` (both imported) are the two finiteness
  conditions on an algebra sheaf, stated on the sections over an affine open, in the shape of
  `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral`.

## Main results

* `Stacks.AffineAlgebraEquivalence.isFinite_relativeSpecToBase`: the relative spectrum of a
  finite quasi-coherent algebra sheaf is finite over the base.
* `Stacks.AffineAlgebraEquivalence.locallyOfFinitePresentation_relativeSpecToBase` and
  `Stacks.AffineAlgebraEquivalence.finitePresentation_relativeSpecToBase`: it is locally of
  finite presentation, resp. of finite presentation, when the algebra sheaf is of finite
  presentation, resp. finite and of finite presentation.

## Implementation notes

The two proofs both rest on `Stacks.AffineAlgebraEquivalence.structureMap_comp_sectionsIso`: over
an affine open `U` of the base, the identification
`Γ(relativeSpec A, relativeSpecToBase A ⁻¹ᵁ U) ≅ A(U)` carries the structure morphism of the
relative spectrum to the structure morphism of the algebra. Finiteness is therefore the
corresponding ring-level statement up to an isomorphism, and is checked directly against the
`finite_app` field of `AlgebraicGeometry.IsFinite`. Finite presentation is not a condition on the
sections over the affine opens of the target alone, so it is checked after restricting to an
affine open, where both source and target are affine and
`AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine` applies.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

-- `Stacks.RelativeSpec.AlgebraSheaf.IsFinite` and
-- `Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation`, the conditions that the structural
-- ring map be module-finite, resp. of finite presentation, on the sections over every affine
-- open, are defined in `StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness` and
-- imported above; the definitions are not repeated here.

end Stacks.RelativeSpec.AlgebraSheaf

namespace Stacks.AffineAlgebraEquivalence

variable {S : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf S)
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]

/-- Over an affine open `U` of the base, the structure morphism of the relative spectrum read on
sections is the structure morphism of the algebra followed by the inverse of the identification
`Γ(relativeSpec A, relativeSpecToBase A ⁻¹ᵁ U) ≅ A(U)`. -/
theorem relativeSpecToBase_app_eq (U : S.affineOpens) :
    (relativeSpecToBase A).app (U : S.Opens) =
      A.hom.hom.app (op (U : S.Opens)) ≫ (sectionsIso A U).inv :=
  ((sectionsIso A U).eq_comp_inv).mpr (structureMap_comp_sectionsIso A U)

/-- The relative spectrum of a finite quasi-coherent algebra sheaf is finite over the base. -/
theorem isFinite_relativeSpecToBase
    (hA : Stacks.RelativeSpec.AlgebraSheaf.IsFinite A) :
    IsFinite (relativeSpecToBase A) where
  finite_app := fun U hU => by
    rw [relativeSpecToBase_app_eq A ⟨U, hU⟩]
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).mpr (hA U hU)

/-- The relative spectrum of a quasi-coherent algebra sheaf of finite presentation is locally of
finite presentation over the base. -/
theorem locallyOfFinitePresentation_relativeSpecToBase
    (hA : Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation A) :
    LocallyOfFinitePresentation (relativeSpecToBase A) := by
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FinitePresentation)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
    (iSup_affineOpens_eq_top S)]
  intro U
  have : IsAffine (relativeSpecToBase A ⁻¹ᵁ (U : S.Opens)).toScheme :=
    isAffineOpen_preimage_relativeSpecToBase A U
  have : IsAffine (U : S.Opens).toScheme := U.2
  have key : RingHom.FinitePresentation
      ((relativeSpecToBase A).app ((U : S.Opens).ι ''ᵁ ⊤)).hom := by
    rw [Scheme.Opens.ι_image_top, relativeSpecToBase_app_eq A U]
    exact (RingHom.finitePresentation_respectsIso.cancel_right_isIso _ _).mpr
      (hA (U : S.Opens) U.2)
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)
    (Q := RingHom.FinitePresentation), morphismRestrict_appTop]
  exact (RingHom.finitePresentation_respectsIso.cancel_right_isIso _ _).mpr key

/-- The relative spectrum of a finite quasi-coherent algebra sheaf of finite presentation is of
finite presentation over the base. -/
theorem finitePresentation_relativeSpecToBase
    (hAfin : Stacks.RelativeSpec.AlgebraSheaf.IsFinite A)
    (hAfp : Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation A) :
    FinitePresentation (relativeSpecToBase A) :=
  have := isFinite_relativeSpecToBase A hAfin
  ⟨locallyOfFinitePresentation_relativeSpecToBase A hAfp, inferInstance, inferInstance⟩

end Stacks.AffineAlgebraEquivalence

end
