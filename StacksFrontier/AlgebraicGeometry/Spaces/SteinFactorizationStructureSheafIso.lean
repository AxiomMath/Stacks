module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnder
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationQcqs

/-!
# The Stein factorization of a universally closed morphism: `Y'` is its own normalization

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S`, and let `X ⟶ Y' ⟶ Y` be its factorization through the normalization
`ν : Y' ⟶ Y` of `Y` in `X` (Stacks 0822, `AlgebraicGeometry.Space.normalizationInQcqs`).  This
file proves that the normalization `Y'' ⟶ Y'` of `Y'` in `X` along the first factor
`f' : X ⟶ Y'` is an isomorphism.  The permanence properties of `f'` (quasi-compact, universally
closed: Stacks 03KS, 04NX) are in
`StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationGeneral`;
quasi-separatedness (Stacks 03KR) and clause (3) of Stacks 0A19 and of Stacks 0A1C,
`f'_* 𝒪_X = 𝒪_{Y'}`, are `AlgebraicGeometry.Space.isQuasiSeparated_toNormalizationInQcqs` and
`AlgebraicGeometry.Space.isIso_fSharp_toNormalizationInQcqs`
(`StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationQcqs`).

## Main results

* `AlgebraicGeometry.Space.isIso_normalizationInQcqsHom_toNormalizationInQcqs`: the
  normalization of `Y'` in `X` along `f'` is `Y'` itself.

## Implementation notes

By the last clause of Stacks 0823
(`AlgebraicGeometry.Space.isRelativeNormalization_comparison_normalizationInQcqs`), applied to the
integral morphism `ν` itself and the identity of `Y'`, the identity of `Y'` is the normalization
of `Y'` in `X`, so `Y'' ⟶ Y'` is an isomorphism.

## References

* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0A1C](https://stacks.math.columbia.edu/tag/0A1C)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-! ### The normalization of `Y'` in `X` -/

/-- **The normalization of `Y'` in `X` along `f'` is `Y'`.**  By the last clause of
Stacks 0823, applied to the integral morphism `ν : Y' ⟶ Y` and the identity of `Y'`, the identity
of `Y'` is the normalization of `Y'` in `X`; so the normalization morphism of `Y'` in `X` is an
isomorphism. -/
theorem isIso_normalizationInQcqsHom_toNormalizationInQcqs :
    IsIso (normalizationInQcqsHom B S hS (toNormalizationInQcqs f hfqc hfqs)
      (isQuasiCompact_toNormalizationInQcqs B S hS f hfqc hfqs)
      (isQuasiSeparated_toNormalizationInQcqs f hfqc hfqs)) := by
  obtain ⟨-, hgqc, hgqs, e, ⟨-, he⟩, -⟩ :=
    isRelativeNormalization_comparison_normalizationInQcqs f hfqc hfqs
      (normalizationInQcqsHom B S hS f hfqc hfqs)
      (isIntegralHom_normalizationInQcqsHom f hfqc hfqs) (toNormalizationInQcqs f hfqc hfqs)
      (toNormalizationInQcqs_comp f hfqc hfqs) (𝟙 _) (Category.comp_id _) (Category.id_comp _)
  have h : IsIso (normalizationInQcqsHom B S hS (toNormalizationInQcqs f hfqc hfqs)
      hgqc hgqs).hom := by
    rw [← he]
    exact (inferInstance : IsIso e.hom)
  have : IsIso ((ObjectProperty.ι (fun F => IsAlgebraicSpace B S hS F)).map
      (normalizationInQcqsHom B S hS (toNormalizationInQcqs f hfqc hfqs)
        (isQuasiCompact_toNormalizationInQcqs B S hS f hfqc hfqs)
        (isQuasiSeparated_toNormalizationInQcqs f hfqc hfqs))) := h
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

end AlgebraicGeometry.Space

end
