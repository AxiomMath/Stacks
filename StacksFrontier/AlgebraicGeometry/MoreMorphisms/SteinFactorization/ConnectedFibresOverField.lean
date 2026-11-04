module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.GeomConnectedFibres.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Proper
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.UniversallyClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative normalization of a field in a proper scheme

Let `k` be a field and let `f : X ⟶ Spec k` be a proper morphism.  This file identifies the
relative normalization `f.normalization` of `Spec k` in `X` with `Spec Γ(X, ⊤)`, compatibly with
the canonical morphisms out of `X`, and deduces that `f.toNormalization` has geometrically
connected fibres.

The identification holds because `Γ(X, ⊤)` is already integral over `k`, so the integral closure
of `k` in `Γ(X, ⊤)` — which is what the sections of the relative normalization compute — is all
of `Γ(X, ⊤)`. This is the base-affine case of
`AlgebraicGeometry.Scheme.Hom.isIso_toNormalization_app`.

## Main results

* `Stacks.SteinFactorization.isAffine_normalization_of_isAffine`: the relative normalization of
  an affine scheme in any scheme is affine.
* `Stacks.SteinFactorization.isIso_appTop_toNormalization`: for `f` proper over a field, the
  canonical map `Γ(f.normalization, ⊤) ⟶ Γ(X, ⊤)` is an isomorphism.
* `Stacks.SteinFactorization.normalizationIsoSpecΓ`: the resulting isomorphism
  `f.normalization ≅ Spec Γ(X, ⊤)`, which carries `f.toNormalization` to `X.toSpecΓ`.
* `Stacks.SteinFactorization.geometricallyConnected_toNormalization_over_field`: for `f` proper
  over a field, `f.toNormalization` has geometrically connected fibres.

The last result is the base-is-a-field case of the connectedness assertion in clause (1) of
[Stacks, Tag 03H2]; it is obtained from [Stacks, Tag 0FD1] through the identification above.
Tag 03H2 itself asserts the same over an arbitrary base.

## References

* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.SteinFactorization

/-- The relative normalization of an affine scheme in any scheme is affine, because the
morphism from the relative normalization to the base is integral, hence affine. -/
public instance isAffine_normalization_of_isAffine {X S : Scheme.{u}} (g : X ⟶ S) [IsAffine S]
    [QuasiCompact g] [QuasiSeparated g] : IsAffine g.normalization :=
  isAffine_of_isAffineHom g.fromNormalization

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- For `f : X ⟶ Spec k` proper over a field, the canonical map from the sections of the
relative normalization to the sections of `X` is an isomorphism: the sections of the relative
normalization are the integral closure of `k` in `Γ(X, ⊤)`, and `Γ(X, ⊤)` is already integral
over `k`. -/
public instance isIso_appTop_toNormalization [IsProper f] :
    IsIso f.toNormalization.appTop := by
  have h := Scheme.Hom.isIso_toNormalization_app f (isAffineOpen_top (Spec (.of k)))
  change IsIso (f.toNormalization.app ⊤)
  rwa [Scheme.Hom.preimage_top] at h

/-- For `f : X ⟶ Spec k` proper over a field, the relative normalization of `Spec k` in `X` is
the spectrum of the ring of global sections of `X`. -/
@[sga "1 X 1.2" "Y′ ≅ Spec f_*O_X"]
public noncomputable def normalizationIsoSpecΓ [IsProper f] :
    f.normalization ≅ Spec Γ(X, ⊤) :=
  f.normalization.isoSpec ≪≫ asIso (Spec.map (inv f.toNormalization.appTop))

/-- The isomorphism `normalizationIsoSpecΓ` carries the canonical morphism to the relative
normalization to the canonical morphism `X ⟶ Spec Γ(X, ⊤)`. -/
public theorem toNormalization_normalizationIsoSpecΓ_hom [IsProper f] :
    f.toNormalization ≫ (normalizationIsoSpecΓ f).hom = X.toSpecΓ := by
  rw [normalizationIsoSpecΓ, Iso.trans_hom, asIso_hom, Scheme.isoSpec_hom, ← Category.assoc,
    Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id,
    Category.comp_id]

open Stacks.AlgebraicGeometry.ProperGeomConnected in
/-- **The base-is-a-field case of the connectedness assertion in clause (1) of
[Stacks, Tag 03H2].** For a proper morphism `f : X ⟶ Spec k` over a field, the canonical
morphism to the relative normalization of `Spec k` in `X` has geometrically connected fibres.

This is [Stacks, Tag 0FD1] transported along `normalizationIsoSpecΓ`. -/
public theorem geometricallyConnected_toNormalization_over_field [IsProper f] :
    GeometricallyConnected f.toNormalization := by
  have hgc : GeometricallyConnected (f.toNormalization ≫ (normalizationIsoSpecΓ f).hom) := by
    rw [toNormalization_normalizationIsoSpecΓ_hom]
    exact geometricallyConnected_toSpecΓ_of_isProper_over_field k X f
  have hresp : MorphismProperty.RespectsIso @GeometricallyConnected := by
    rw [GeometricallyConnected.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  exact (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected
    f.toNormalization (normalizationIsoSpecΓ f).hom).mp hgc

end Stacks.SteinFactorization
