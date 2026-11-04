module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineImmersion

/-!
# Affineness of a quasi-compact immersion into an affine scheme

Let `j : V ⟶ Spec A` be a quasi-compact immersion and let `f ∈ A` be such that the inverse
image of the standard open `D(f)` is affine and the part of the image of `j` outside `D(f)`
is closed. Then `V` is affine.

## Main results

* `AlgebraicGeometry.isAffine_of_isImmersion_of_isAffineOpen_preimage_basicOpen`: the
  affineness criterion.

## Implementation notes

This is the criterion of
`AlgebraicGeometry.isAffine_of_isAffineHom_restrict_of_isClosed` applied to the standard open:
the inclusion of a standard open of an affine scheme is an affine morphism, and so is the
restriction of `j` over it because both its source and its target are affine. The standard open
is written as `Scheme.basicOpen` of the global section corresponding to `f`, which the
affineness hypothesis identifies with `PrimeSpectrum.basicOpen f`.

## References

* [Stacks Project, Tag 0ABH](https://stacks.math.columbia.edu/tag/0ABH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0ABH.** A quasi-compact immersion into an affine scheme whose
restriction over a standard open is affine and the remainder of whose image is closed has an
affine source. -/
@[stacks 0ABH]
theorem isAffine_of_isImmersion_of_isAffineOpen_preimage_basicOpen {A : Type u} [CommRing A]
    {V : Scheme.{u}} (j : V ⟶ Spec (CommRingCat.of A)) [IsImmersion j] [QuasiCompact j]
    (f : A) (hD : IsAffineOpen (j ⁻¹ᵁ PrimeSpectrum.basicOpen f))
    (hclosed : IsClosed (Set.range (j : V → Spec (CommRingCat.of A)) ∩
      ((Spec (CommRingCat.of A)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f) :
          Set (Spec (CommRingCat.of A)))ᶜ)) : IsAffine V := by
  let X : Scheme.{u} := Spec (CommRingCat.of A)
  let U : X.Opens := X.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)
  have hU : U = PrimeSpectrum.basicOpen f :=
    basicOpen_eq_of_affine (R := CommRingCat.of A) (f := (f : CommRingCat.of A))
  have : IsAffine U := (isAffineOpen_top X).basicOpen _
  have : IsAffine (j ⁻¹ᵁ U) := by rwa [hU]
  have : IsAffineHom U.ι := isAffineHom_of_isAffine _
  have : IsAffineHom (j ∣_ U) := isAffineHom_of_isAffine _
  exact isAffine_of_isAffineHom_restrict_of_isClosed j U hclosed

end AlgebraicGeometry

end
