module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.Polynomial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Proj_S(𝒪_S[T]) ≅ S`

The relative homogeneous spectrum of the one-variable polynomial algebra of a scheme is that
scheme: `Proj_S(𝒪_S[T]) ≅ ℙ⁰_S ≅ S`, and the composite isomorphism is the canonical morphism
`Proj_S(𝒪_S[T]) ⟶ S` of the relative `Proj`, so it is an isomorphism over `S`.

Both halves are already proved.
`Stacks.AlgebraicGeometry.ProjPolynomialSections.exists_iso_relativeProj_polyAlgebra` is the first
at every `n`, and `AlgebraicGeometry.projectiveSpaceOver.zeroIsoBase` is the second; this file is
their composition at `n = 0`, read so that the canonical morphism survives.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolynomialSections.exists_iso_base_relativeProj_polyAlgebra_zero`:
  **`Proj_S(𝒪_S[T]) ≅ S` over `S`.**
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.isIso_relativeProjToBase_polyAlgebra_zero`: the
  canonical morphism `Proj_S(𝒪_S[T]) ⟶ S` is an isomorphism.

## Implementation notes

**The one-variable algebra is `polyAlgebra 0`, not a separate construction.**
`Stacks.AlgebraicGeometry.ProjPolynomialSections.polyAlgebra n S` has `n + 1` variables, so at
`n = 0` its sections over an affine open `U` are `Γ(S, U)[T₀]`: it is `𝒪_S[T]` with no
intervening identification.

**The result is stated existentially because its first half is.** The isomorphism of
`exists_iso_relativeProj_polyAlgebra` is produced from a choice of charts and is not a named
definition, so there is no isomorphism here to name either; what a consumer needs is the
isomorphism together with the equation saying it is the canonical morphism, and that is what the
existential carries. `isIso_relativeProjToBase_polyAlgebra_zero` is the part of it that needs no
choice.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01MI](https://stacks.math.columbia.edu/tag/01MI)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)

## Not done here

**No project tag is attached.** `Proj_S(𝒪_S[T]) ≅ S` over a general base scheme `S` is not a
labelled assertion of any of the four nearby tags.

* Tag 01NF and Tag 01NN assert the construction of projective space and the glueing of the
  relative `Proj`, both already formalized; this is the reason recorded in the `Not done here`
  section of `StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.Polynomial`.
* Tag 01MI, Example 27.8.14, is the *absolute* case: for a ring `A` and `S = A[T]` with `T` in
  degree one, the canonical morphism `Proj(S) ⟶ Spec(A)` is an isomorphism. That is a formalized
  and registered result, `AlgebraicGeometry.ProjectiveSpace.isIso_toSpecZero_oneVariable` of
  `StacksFrontier.AlgebraicGeometry.Constructions.ProjOfPolynomialOneVariable`, and it is an input
  to `AlgebraicGeometry.projectiveSpaceOver.zeroIsoBase` used below. The relative statement over
  an arbitrary base scheme is strictly more than the tag asserts, so the tag is not repeated
  here.
* Tag 01OE, Lemma 27.21.5, states that `ℙⁿ_S` is a projective bundle over `S`. The
  identification `ℙⁿ_S = Proj_S(𝒪_S[T₀, …, Tₙ])` appears only inside its *proof*, not in its
  statement, so `exists_iso_relativeProj_polyAlgebra` and the `n = 0` reading below are a step
  of that proof rather than the lemma. Tag 01OE is registered on
  `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace` of
  `StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceMorphism`.

**Nothing here is about the graded algebra `Sym^*(𝒞)[T]`.** This result is the map `i` of
Lemma 42.55.2 (Tag 0FEF) at the one place that lemma needs it, namely the source
`X = Proj_X(𝒪_X[T])`; the target `E = Proj_X(Sym^*(𝒞)[T])` needs the sheaf-level graded algebra
`Sym^*(𝒞)[T]`, which the library does not have, so no part of Tag 0FEF is claimed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue

namespace Stacks.AlgebraicGeometry.ProjPolynomialSections

universe u

variable (S : Scheme.{u})

/-- **`Proj_S(𝒪_S[T]) ≅ S` over `S`**: the relative homogeneous spectrum of the one-variable
polynomial algebra of a scheme is that scheme, by an isomorphism whose forward direction is the
canonical morphism of the relative `Proj`. It is `Proj_S(𝒪_S[T]) ≅ ℙ⁰_S` followed by
`ℙ⁰_S ≅ S`. -/
@[ega "II 3.1.7"]
public theorem exists_iso_base_relativeProj_polyAlgebra_zero :
    ∃ e : relativeProj (polyAlgebra 0 S) ≅ S,
      e.hom = relativeProjToBase (polyAlgebra 0 S) := by
  obtain ⟨e, he⟩ := exists_iso_relativeProj_polyAlgebra 0 S
  refine ⟨e ≪≫ projectiveSpaceOver.zeroIsoBase S, ?_⟩
  rw [Iso.trans_hom, projectiveSpaceOver.zeroIsoBase_hom]
  exact he

/-- **The canonical morphism `Proj_S(𝒪_S[T]) ⟶ S` is an isomorphism.** -/
public theorem isIso_relativeProjToBase_polyAlgebra_zero :
    IsIso (relativeProjToBase (polyAlgebra 0 S)) := by
  obtain ⟨e, he⟩ := exists_iso_base_relativeProj_polyAlgebra_zero S
  rw [← he]
  infer_instance

end Stacks.AlgebraicGeometry.ProjPolynomialSections

end
