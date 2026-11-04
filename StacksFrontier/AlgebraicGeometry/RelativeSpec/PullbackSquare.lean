module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restriction squares of relative spectra

For nested affine opens `U ≤ U'` of a scheme `X` and a sheaf of algebras over the structure
sheaf, the square formed by the spectra of the algebra's sections, the two open subschemes,
and the restriction morphisms is cartesian as soon as the corresponding square of rings is a
pushout.

## Main results

* `specMap_restrict_isoSpec_inv` identifies the spectrum of a restriction map of the
  structure sheaf between affine opens with the inclusion of open subschemes, conjugated by
  the canonical affine isomorphisms.
* `isPullback_specMap_of_isPushout` is the cartesian-square statement: a pushout square of
  rings over a pair of nested affine opens induces a cartesian square of spectra over those
  opens.

## Implementation notes

The quasi-coherence of the algebra enters only through the pushout hypothesis
`B(U) ≅ B(U') ⊗_{Γ(X, U')} Γ(X, U)`, which is kept as an explicit argument here. That keeps
this file independent of the quasi-coherent base-change comparison, which is what supplies
the hypothesis for an actual quasi-coherent algebra.

The reduction is in two steps. `specMap_restrict_isoSpec_inv` moves the bottom edge of the
square from `Spec Γ(X, U) ⟶ Spec Γ(X, U')` to `U ⟶ U'`; it is proved by cancelling the
isomorphism `hU.isoSpec.hom`, which is `Scheme.Opens.toSpecΓ`, and then applying the
naturality of `toSpecΓ` in the open. With that in hand
`AlgebraicGeometry.isPullback_SpecMap_of_isPushout` turns the pushout of rings into a
cartesian square of affine spectra, and `CategoryTheory.IsPullback.of_iso` transports it
along the two canonical affine isomorphisms, the identity on the two upper corners.

## References

* [Stacks Project, Tag 01LN](https://stacks.math.columbia.edu/tag/01LN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec

variable {X : Scheme.{u}}

/-- For nested affine opens `U ≤ U'`, the spectrum of the restriction map on the structure
sheaf is the inclusion `U ⟶ U'` of open subschemes, conjugated by the canonical affine
isomorphisms. -/
theorem specMap_restrict_isoSpec_inv {U U' : X.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (h : U ≤ U') :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ hU'.isoSpec.inv =
      hU.isoSpec.inv ≫ X.homOfLE h := by
  rw [← cancel_epi hU.isoSpec.hom, Iso.hom_inv_id_assoc, hU.isoSpec_hom,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, hU'.toSpecΓ_isoSpec_inv,
    Category.comp_id]

/-- **Stacks Project, Tag 01LN**, with quasi-coherence supplied as a pushout hypothesis. For
nested affine opens `U ≤ U'`, a pushout square of rings over the restriction map induces a
cartesian square of spectra over the two open subschemes. -/
theorem isPullback_specMap_of_isPushout {U U' : X.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (h : U ≤ U') {B B' : CommRingCat.{u}}
    (a : Γ(X, U) ⟶ B) (a' : Γ(X, U') ⟶ B') (r : B' ⟶ B)
    (hpush : IsPushout a' (X.presheaf.map (homOfLE h).op) r a) :
    IsPullback (Spec.map r) (Spec.map a ≫ hU.isoSpec.inv)
      (Spec.map a' ≫ hU'.isoSpec.inv) (X.homOfLE h) :=
  (isPullback_SpecMap_of_isPushout a' (X.presheaf.map (homOfLE h).op) r a hpush).of_iso
    (Iso.refl _) (Iso.refl _) hU.isoSpec.symm hU'.isoSpec.symm
    (by simp) (by simp) (by simp)
    (by simpa using specMap_restrict_isoSpec_inv hU hU' h)

end Stacks.RelativeSpec

end
