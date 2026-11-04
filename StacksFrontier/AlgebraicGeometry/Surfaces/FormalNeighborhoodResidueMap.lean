module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField

/-!
# The residue map of the formal neighbourhood of an exceptional curve

The projection of the formal neighbourhood `A = lim Γ(X, 𝒪_X/ℐⁿ)` to the first thickening lands in
`Γ(E, 𝒪_E)`, which a choice of isomorphism `𝐏¹_k ≅ E` identifies with `k`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodResidue`: the residue map `A ⟶ k`.
* `AlgebraicGeometry.Scheme.IdealSheafData.surjective_formalNeighborhoodResidue`: it is surjective
  when the projection to the first thickening is.
* `AlgebraicGeometry.Scheme.IdealSheafData.ker_formalNeighborhoodResidue`: its kernel is the first
  step of the projection-kernel filtration.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]

/-! ### The residue map to the ground field -/

/-- **The residue map of the formal neighbourhood, `A ⟶ k`.**

The projection to the first thickening lands in `Γ(E, 𝒪_E)`, which a choice of isomorphism
`e : 𝐏¹_k ≅ E` identifies with `k` by
`AlgebraicGeometry.Scheme.IdealSheafData.sectionsSubschemeRingEquivOfIso`; this is that
composite. The first thickening is `(D ^ 1).subscheme` where `e` presents `D.subscheme`, so the
isomorphism is transported along `pow_one D` before being applied.

Unlike `RingHom.quotientKerEquivOfSurjective`, which presents the residue ring as a quotient,
this is a ring map out of `A` itself, so it can be used where a `k`-structure is wanted without
forming the quotient. It is the `φ` input of `AlgebraicGeometry.Scheme.IdealSheafData`
`.le_span_pow_sup_iff_coeff_mem_one_of_gradedPiece`. -/
public def formalNeighborhoodResidue (e : projectiveLineProj k ≅ D.subscheme) :
    formalNeighborhoodRing D →+* k :=
  (sectionsSubschemeRingEquivOfIso (D ^ 1) k
      (e ≪≫ (eqToIso (congrArg (fun J : X.IdealSheafData => J.subscheme)
        (pow_one D))).symm)).toRingHom.comp
    (formalNeighborhoodProjection D 0)

/-- **The residue map is surjective** when the projection to the first thickening is, being that
projection followed by a ring isomorphism. -/
public theorem surjective_formalNeighborhoodResidue
    (hsurj : Function.Surjective (formalNeighborhoodProjection D 0))
    (e : projectiveLineProj k ≅ D.subscheme) :
    Function.Surjective (formalNeighborhoodResidue D k e) :=
  (sectionsSubschemeRingEquivOfIso (D ^ 1) k _).surjective.comp hsurj

/-- **The kernel of the residue map is the first step of the projection-kernel filtration.**
Composing with a ring isomorphism does not change a kernel, and the first step of the filtration
is by definition the kernel of the projection to the first thickening. -/
public theorem ker_formalNeighborhoodResidue (e : projectiveLineProj k ≅ D.subscheme) :
    RingHom.ker (formalNeighborhoodResidue D k e) = formalNeighborhoodFiltration D 1 :=
  (RingHom.ker_equiv_comp (formalNeighborhoodProjection D 0)
      (sectionsSubschemeRingEquivOfIso (D ^ 1) k _)).trans
    (formalNeighborhoodFiltration_succ D 0).symm

end AlgebraicGeometry.Scheme.IdealSheafData

end
