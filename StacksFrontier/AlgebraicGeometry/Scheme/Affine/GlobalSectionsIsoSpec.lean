module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Global sections of the affine comparison of an affine open

Let `V` be an affine open of a scheme `X`. Reading the comparison `V ≅ Spec Γ(X, V)` as a
morphism of ringed spaces and taking global sections gives a ring map
`Γ(Spec Γ(X, V), ⊤) → Γ(V, ⊤)`; composed with `Γ(X, V) ≅ Γ(Spec Γ(X, V), ⊤)` it is the
restriction map `Γ(X, V) → Γ(V, ⊤)` of `𝒪_X`, that is, the inverse of
`AlgebraicGeometry.Scheme.Opens.topIso`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.ΓSpecIso_inv_comp_Γ_map_isoSpec_hom`
* `AlgebraicGeometry.IsAffineOpen.Γ_map_isoSpec_hom_comp_ΓSpecIso_inv_hom`: the same identity
  between the underlying ring homomorphisms.

## Implementation notes

The content is `AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop`; what the statement adds is
that global sections of the underlying morphism of ringed spaces, in the spelling
`CategoryTheory.SheafedSpace.Γ` in which the sheafification constructions of Stacks 01BH and
01BJ are phrased, is the scheme-level `AlgebraicGeometry.Scheme.Hom.appTop`. The two are equal by
definition, so the proof is a `change` followed by the scheme-level identity.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.IsAffineOpen

universe u

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

/-- **Global sections of `V ≅ Spec Γ(X, V)` is the restriction map of `𝒪_X` to `V`.** -/
theorem ΓSpecIso_inv_comp_Γ_map_isoSpec_hom :
    (Scheme.ΓSpecIso Γ(X, V)).inv ≫
        SheafedSpace.Γ.map (hV.isoSpec.hom.toLRSHom.toShHom).op =
      V.topIso.inv := by
  show (Scheme.ΓSpecIso Γ(X, V)).inv ≫ hV.isoSpec.hom.appTop = V.topIso.inv
  rw [hV.isoSpec_hom_appTop, Iso.inv_hom_id_assoc]

/-- The ring-homomorphism form of `ΓSpecIso_inv_comp_Γ_map_isoSpec_hom`: the scalar map along
which a `Γ(X, V)`-module is turned into a sheaf of `𝒪_V`-modules. -/
theorem Γ_map_isoSpec_hom_comp_ΓSpecIso_inv_hom :
    (SheafedSpace.Γ.map (hV.isoSpec.hom.toLRSHom.toShHom).op).hom.comp
        (Scheme.ΓSpecIso Γ(X, V)).inv.hom =
      V.topIso.inv.hom := by
  show ((Scheme.ΓSpecIso Γ(X, V)).inv ≫ hV.isoSpec.hom.appTop).hom = _
  rw [hV.isoSpec_hom_appTop, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.IsAffineOpen

end
