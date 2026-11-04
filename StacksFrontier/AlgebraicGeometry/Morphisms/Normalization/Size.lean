module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Size.Pullback

/-!
# The size of a relative normalization

The *size* of a scheme (`AlgebraicGeometry.Scheme.size`, Tag 000I) is the maximum of `ℵ₀`, the
number of its affine opens, and the cardinalities of its rings of sections over affine opens.
Tag 000R lists the constructions under which a size bound is preserved; the relative
normalization of Tag 035H is not among them, and this file supplies the missing clause: for a
quasi-compact quasi-separated morphism `f : X ⟶ Y` of schemes,

`size (f.normalization) ≤ max (size X) (size Y)`.

This is the bound a big site needs in order to contain the relative normalization of a morphism
of its objects.

## Main results

* `AlgebraicGeometry.Scheme.mk_sections_le_size_of_isCompact`: the sections over a
  quasi-compact open have cardinality at most the size of the scheme.
* `AlgebraicGeometry.Scheme.Hom.size_normalization_le`: the size bound for the relative
  normalization.

## Implementation notes

The proof is clause (9)(e) of Tag 000R — a subring of a ring of bounded cardinality — glued
along clause (6), a small open covering by small opens. The relative normalization is covered
by the preimages `ν⁻¹(U)` of the affine opens `U` of the target, by Mathlib's
`AlgebraicGeometry.Scheme.Hom.fromNormalization_preimage`; each such preimage is affine, since
`ν` is integral, and Mathlib's `AlgebraicGeometry.Scheme.Hom.normalizationObjIso` identifies its
ring of sections with the integral closure of `Γ(Y, U)` in `Γ(X, f⁻¹U)`, a subring of the
latter. Quasi-compactness of `f` makes `f⁻¹U` quasi-compact, so the sheaf separation axiom on a
finite affine covering of it bounds `#Γ(X, f⁻¹U)` by `size X`. The index type of the covering is
the set of affine opens of `Y`, bounded by `size Y`.

Quasi-compactness of `f` is used only through this bound on `#Γ(X, f⁻¹U)`; it is in any case
part of the hypotheses under which Mathlib defines the relative normalization at all.

## References

* [Stacks Project, Tag 000I](https://stacks.math.columbia.edu/tag/000I)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry

/-- The sections of a scheme over a quasi-compact open have cardinality at most the size of the
scheme: such an open is a finite union of affine opens, and the sheaf separation axiom injects
its sections into the finite product of the sections over those. -/
theorem Scheme.mk_sections_le_size_of_isCompact (T : Scheme.{u}) (U : T.Opens)
    (hU : IsCompact (U : Set T)) : #Γ(T, U) ≤ T.size := by
  obtain ⟨s, hs, heq⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  have : Finite s := hs.to_subtype
  have hcov : U = ⨆ i : s, (i.1 : T.Opens) := by
    simpa only [iSup_subtype] using heq
  exact T.mk_sections_le_of_eq_iSup hcov T.aleph0_le_size fun i => T.mk_sections_le_size i.1

namespace Scheme.Hom

/-- **The relative normalization does not increase size.** For a quasi-compact quasi-separated
morphism `f : X ⟶ Y` of schemes, the relative normalization of `Y` in `X` has size at most
`max (size X) (size Y)`.

The normalization is covered by the preimages of the affine opens `U ⊆ Y` under its integral
structure morphism; each is affine with ring of sections the integral closure of `Γ(Y, U)` in
`Γ(X, f⁻¹U)`, hence of cardinality at most `#Γ(X, f⁻¹U) ≤ size X`, and the index type of the
covering is bounded by `size Y`. -/
theorem size_normalization_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    f.normalization.size ≤ max X.size Y.size := by
  have : Nonempty Y.AffineZariskiSite := ⟨⟨⊥, isAffineOpen_bot Y⟩⟩
  have hcov : ⨆ U : Y.AffineZariskiSite, f.fromNormalization ⁻¹ᵁ U.1 = ⊤ := by
    convert f.normalizationOpenCover.iSup_opensRange using 1
    congr 1
    funext U
    exact f.fromNormalization_preimage U
  refine (Scheme.size_le_of_iSup_eq_top
    (fun U : Y.AffineZariskiSite => f.fromNormalization ⁻¹ᵁ U.1) hcov).trans
    (max_le (Y.mk_affineOpens_le_size.trans (le_max_right _ _)) (ciSup_le' fun U => ?_))
  have hV : IsAffineOpen (f.fromNormalization ⁻¹ᵁ U.1) := U.2.preimage f.fromNormalization
  have : IsAffine (f.fromNormalization ⁻¹ᵁ U.1).toScheme := hV
  let _ : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  have hΓ : #Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U.1) ≤ X.size :=
    calc #Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U.1)
        = #(integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)) :=
          mk_congr (f.normalizationObjIso U.2).commRingCatIsoToRingEquiv.toEquiv
      _ ≤ #Γ(X, f ⁻¹ᵁ U.1) := mk_le_of_injective Subtype.val_injective
      _ ≤ X.size := X.mk_sections_le_size_of_isCompact _ (f.isCompact_preimage U.2.isCompact)
  calc ((f.fromNormalization ⁻¹ᵁ U.1 : f.normalization.Opens) : Scheme.{u}).size
      = max ℵ₀ #Γ((f.fromNormalization ⁻¹ᵁ U.1).toScheme, ⊤) := Scheme.size_of_isAffine _
    _ = max ℵ₀ #Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U.1) := by
        rw [Scheme.mk_sections_coe_opens]
    _ ≤ X.size := max_le X.aleph0_le_size hΓ
    _ ≤ max X.size Y.size := le_max_left _ _

end Scheme.Hom

end AlgebraicGeometry

end
