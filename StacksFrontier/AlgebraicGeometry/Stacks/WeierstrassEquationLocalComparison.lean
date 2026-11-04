module

public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCoordinateChangeTorsor

/-!
# A Weierstrass equation over an affine open gives a triple with the Weierstrass family

Let `E` be a pointed family over a scheme `S` and `U` an affine open of `S`. If the restriction
of `E` to `U` is isomorphic to the plane cubic of a Weierstrass equation `C` over `Γ(S, U)` with
invertible discriminant, then `E` has a Weierstrass equation over `U` in the sense used by
Tag 072T: there is a triple `(a, a', α)` comparing the Weierstrass family `(E_W, f_W, 0_W)` with
`E` over `U` whose morphism to `S` is the inclusion of `U`. The morphism `a : U ⟶ W` is the one
classifying `C`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_comparison_of_familyIso`: the
  statement above.

## References

* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

/-- If the restriction of a pointed family `E` over `S` to an affine open `U` is isomorphic to the
plane cubic of a Weierstrass equation `C` over `Γ(S, U)` with invertible discriminant, pulled
back along `U ≅ Spec Γ(S, U)`, then `U` carries a triple comparing the Weierstrass family with
`E` whose morphism to `S` is the inclusion of `U`. -/
theorem exists_comparison_of_familyIso {S : Scheme.{u}} (E : PointedFamily S) {U : S.Opens}
    (hU : IsAffineOpen U) {s : S} (hs : s ∈ U) (C : WeierstrassCurve Γ(S, U)) [C.IsElliptic]
    (e : FamilyIso ((familyOf C).pullback hU.isoSpec.hom) (E.pullback U.ι)) :
    ∃ V : S.Opens, s ∈ V ∧ ∃ x : Comparison family.{u} E V.toScheme, x.snd = V.ι := by
  let φ := baseRingHom C
  let e₁ : FamilyIso (family.{u}.pullback (hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)))
      ((family.{u}.pullback (Spec.map (CommRingCat.ofHom φ))).pullback hU.isoSpec.hom) :=
    (PointedFamily.pullbackPullbackIso family.{u} _ hU.isoSpec.hom rfl).symm
  let e₂ : FamilyIso ((family.{u}.pullback (Spec.map (CommRingCat.ofHom φ))).pullback
      hU.isoSpec.hom) ((familyOf C).pullback hU.isoSpec.hom) :=
    ((familyOfMapIso curve.{u} φ).trans (familyOfEq (curve_map_baseRingHom C))).pullback _
  exact ⟨U, hs, Comparison.ofFamilyIso _ U.ι ((e₁.trans e₂).trans e), rfl⟩

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
