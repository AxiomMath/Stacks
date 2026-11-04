module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodFiltration
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningRestriction

/-!
# The residue ring of the formal neighbourhood of an exceptional curve is a field

Let `D` be an ideal sheaf on a scheme `X` whose subscheme `E` is isomorphic to the projective line
`𝐏¹_k` over a field `k`, and let `A` be
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing D`, the ring of compatible global
functions on the infinitesimal thickenings of `D`. If the projection `A ⟶ Γ(E, 𝒪_E)` is
surjective, its kernel `I₁` is the first step of the projection-kernel filtration and

`A / I₁ ≅ Γ(E, 𝒪_E) ≅ Γ(𝐏¹_k, 𝒪) ≅ k`,

so the residue ring `A / I₁` is a field.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isField_sections_subscheme_of_iso_projectiveLineProj` —
  the global functions on a subscheme isomorphic to `𝐏¹_k` form a field.
* `AlgebraicGeometry.Scheme.IdealSheafData.isField_quotient_formalNeighborhoodFiltration_one` —
  the residue ring `A / I₁` is a field, for a surjective projection and a subscheme isomorphic
  to the projective line.
* `AlgebraicGeometry.Scheme.IdealSheafData.isField_quotient_of_isExceptionalCurveOfFirstKind` —
  the same for an exceptional curve of the first kind with surjective transition maps.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]

/-- The ring isomorphism `Γ(E, 𝒪_E) ≅ Γ(𝐏¹_k, 𝒪) ≅ k` for a closed subscheme `E` isomorphic to
the projective line over a field `k`. -/
public def sectionsSubschemeRingEquivOfIso (e : projectiveLineProj k ≅ D.subscheme) :
    Γ(D.subscheme, ⊤) ≃+* k :=
  (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv.trans
    (Stacks.ProjectiveSpace.Cohomology.coeffRingEquivGlobalSections k 1).symm

/-- The global functions on a closed subscheme isomorphic to the projective line over a field
form a field. -/
public theorem isField_sections_subscheme_of_iso_projectiveLineProj
    (e : projectiveLineProj k ≅ D.subscheme) : IsField Γ(D.subscheme, ⊤) :=
  MulEquiv.isField (Field.toIsField k) (sectionsSubschemeRingEquivOfIso D k e).toMulEquiv

/-- The global functions on the first infinitesimal thickening of a closed subscheme isomorphic
to the projective line over a field form a field. -/
public theorem isField_sections_thickening_zero (e : projectiveLineProj k ≅ D.subscheme) :
    IsField Γ(thickening D 0, ⊤) := by
  show IsField Γ((D ^ 1).subscheme, ⊤)
  rw [pow_one]
  exact isField_sections_subscheme_of_iso_projectiveLineProj D k e

/-- If the projection of the formal neighbourhood ring onto the first thickening is surjective
and the subscheme is isomorphic to the projective line over a field, then the quotient of the
formal neighbourhood ring by the first step of its projection-kernel filtration is a field. -/
public theorem isField_quotient_formalNeighborhoodFiltration_one
    (hsurj : Function.Surjective (formalNeighborhoodProjection D 0))
    (e : projectiveLineProj k ≅ D.subscheme) :
    IsField (formalNeighborhoodRing D ⧸ formalNeighborhoodFiltration D 1) :=
  MulEquiv.isField (isField_sections_thickening_zero D k e)
    (RingHom.quotientKerEquivOfSurjective hsurj).toMulEquiv

/-- The residue ring of the formal neighbourhood of an exceptional curve of the first kind is a
field, given that the transition maps of the inverse system of thickenings are surjective. -/
public theorem isField_quotient_of_isExceptionalCurveOfFirstKind
    {e : projectiveLineProj k ≅ D.subscheme} (_hE : IsExceptionalCurveOfFirstKind D k e)
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m)) :
    IsField (formalNeighborhoodRing D ⧸ formalNeighborhoodFiltration D 1) :=
  isField_quotient_formalNeighborhoodFiltration_one D k
    (surjective_formalNeighborhoodProjection D hsurj 0) e

end AlgebraicGeometry.Scheme.IdealSheafData

end
