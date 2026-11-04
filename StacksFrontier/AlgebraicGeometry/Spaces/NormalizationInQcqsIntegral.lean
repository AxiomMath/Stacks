module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverPushforwardReflectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# The normalization of an algebraic space in an integral one is that space

Let `f : Y ⟶ X` be an integral morphism of algebraic spaces over `S`.  Stacks 0825 says that the
integral closure of `X` in `Y` — the normalization `ν : X' = \underline{Spec}_X(𝒪') ⟶ X` of
Stacks 0822, with its canonical factorization `Y ⟶ X' ⟶ X` of `f` — is `Y` itself.  This file
proves it for the normalization `AlgebraicGeometry.Space.normalizationInQcqs` with its canonical
morphism `AlgebraicGeometry.Space.toNormalizationInQcqs`: that morphism `f' : Y ⟶ X'` is an
isomorphism.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_isIntegralHom` and
  `AlgebraicGeometry.Space.isQuasiSeparated_of_isIntegralHom`: an integral morphism of algebraic
  spaces is quasi-compact and quasi-separated, so its normalization is defined.
* `AlgebraicGeometry.Space.isIso_toNormalizationInQcqs_of_isIntegralHom`: **Stacks 0825**, the
  canonical morphism `f' : Y ⟶ X'` to the normalization of `X` in `Y` is an isomorphism.
* `AlgebraicGeometry.Space.isIso_toNormalizationInQcqsOver_of_isIntegralHom`: the same, as an
  isomorphism of algebraic spaces over `X`.

## Implementation notes

The source's proof is two citations: by Stacks 0415 an integral morphism is affine and
universally closed, and then the statement is the case of Stacks 0A0Q in which `f` is affine.
Both appear here.  Universal closedness makes `f_* 𝒪_Y` integral over `𝒪_X` (the first assertion
of Stacks 0A0Q), so the inclusion `𝒪' ⊂ f_* 𝒪_Y` is an isomorphism; affineness makes `Y` an
algebraic space affine over `X`, and between such spaces direct image reflects isomorphisms
(`AlgebraicGeometry.Space.isIso_of_pushforwardAlgebraMap_eq_integralClosureInclusion`).

What is needed of `f'` is that its direct-image map is `ν_* 𝒪_{X'} ≅ 𝒪' ⊂ f_* 𝒪_Y`.  For an
affine `f` the source `Y` is representable over `X`, so fullness of direct image produces a
morphism `g : Y ⟶ X'` over `X` with exactly that direct-image map; precomposed with any point of
`Y` it has the direct-image map characterizing `f'`
(`AlgebraicGeometry.Space.eq_toNormalizationInQcqsOver`), so `g = f'`.

## References

* [Stacks Project, Tag 0825](https://stacks.math.columbia.edu/tag/0825)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An integral morphism of algebraic spaces is quasi-compact.**  It is affine, and an affine
morphism is quasi-compact. -/
theorem isQuasiCompact_of_isIntegralHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hf : IsIntegralHom B S hS f) : IsQuasiCompact B S hS f :=
  isQuasiCompact_of_isAffineHom' B S hS f hF hG (isAffineHom_of_isIntegralHom f hf)

/-- **An integral morphism of algebraic spaces is quasi-separated.**  It is separated, and a
separated morphism is quasi-separated. -/
theorem isQuasiSeparated_of_isIntegralHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hf : IsIntegralHom B S hS f) : IsQuasiSeparated B S hS f :=
  isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isIntegralHom B S hS f hF hG hf)

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0825, over `X`.**  For an integral morphism `f : Y ⟶ X` of algebraic spaces over
`S`, the canonical morphism `f' : Y ⟶ X'` to the normalization of `X` in `Y` is an isomorphism of
algebraic spaces over `X`. -/
theorem isIso_toNormalizationInQcqsOver_of_isIntegralHom (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) :
    IsIso (toNormalizationInQcqsOver f
      (isQuasiCompact_of_isIntegralHom f.hom Y.property X.property hf)
      (isQuasiSeparated_of_isIntegralHom f.hom Y.property X.property hf)) := by
  set hfqc := isQuasiCompact_of_isIntegralHom f.hom Y.property X.property hf
  set hfqs := isQuasiSeparated_of_isIntegralHom f.hom Y.property X.property hf
  obtain ⟨g, hg⟩ := exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS
    (relativelyRepresentable_of_isAffineHom B S hS (Over.mk f).hom
      (isAffineHom_of_isIntegralHom f.hom hf))
    (normalizationInQcqsAffineOver B S hS f hfqc hfqs)
    (normalizationInQcqsAlgebraMap B S hS f hfqc hfqs)
  have hgf : g = toNormalizationInQcqsOver f hfqc hfqs :=
    eq_toNormalizationInQcqsOver f hfqc hfqs g fun T y => by
      rw [pushforwardAlgebraMap_comp, hg]
  rw [← hgf]
  refine isIso_of_pushforwardAlgebraMap_eq_integralClosureInclusion B S hS f hf _ g
    (normalizationInQcqsPushforwardIso B S hS f hfqc hfqs).symm ?_
  rw [hg]
  exact Iso.inv_hom_id_assoc _ _

/-- **Stacks 0825.**  Let `f : Y ⟶ X` be an integral morphism of algebraic spaces over `S`.  Then
the integral closure of `X` in `Y` is equal to `Y`: the canonical morphism `f' : Y ⟶ X'` of
Stacks 0822 from `Y` to the normalization `ν : X' ⟶ X` of `X` in `Y` is an isomorphism.

An integral morphism is quasi-compact and quasi-separated, so the normalization is defined at no
further hypothesis.  By Stacks 0415 `f` is affine and universally closed; universal closedness
makes `f_* 𝒪_Y` integral over `𝒪_X` (Stacks 0A0Q), so the integral closure `𝒪' = ν_* 𝒪_{X'}` is
all of `f_* 𝒪_Y`, and since `Y` and `X'` are both affine over `X`, direct image reflects that
isomorphism of algebras to `f'`. -/
@[stacks 0825]
theorem isIso_toNormalizationInQcqs_of_isIntegralHom (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) :
    IsIso (toNormalizationInQcqs f
      (isQuasiCompact_of_isIntegralHom f.hom Y.property X.property hf)
      (isQuasiSeparated_of_isIntegralHom f.hom Y.property X.property hf)) :=
  have := isIso_toNormalizationInQcqsOver_of_isIntegralHom f hf
  inferInstanceAs (IsIso ((Over.forget X).map (toNormalizationInQcqsOver f
    (isQuasiCompact_of_isIntegralHom f.hom Y.property X.property hf)
    (isQuasiSeparated_of_isIntegralHom f.hom Y.property X.property hf))))

end AlgebraicGeometry.Space

end
