module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureUniversal
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn

/-!
# The normalization of an algebraic space in an integral one

Let `f : Y ⟶ X` be an integral morphism of algebraic spaces over `S`.  Stacks 0825 asserts that
the integral closure of `X` in `Y` — the normalization `ν : X' ⟶ X` of `X` in `Y` of Stacks
0822, the relative spectrum of the integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y` — is `Y` itself,
as an algebraic space over `X`.

## Main results

* `AlgebraicGeometry.Space.normalizationInIsoOfIsIntegralHom`: the normalization of `X` in `Y`
  is canonically isomorphic to `Y` over `X`, when `f` is integral and `f_* 𝒪_Y` is integral
  over `𝒪_X`.
* `AlgebraicGeometry.Space.normalizationInIsoOfIsIntegralHom_w`: that isomorphism is one over
  `X`, composing with `f` to the normalization morphism `ν`.

## Implementation notes

The source's proof is two citations: Stacks 0415 reduces an integral morphism to an affine
universally closed one, and then the statement is the special case of Stacks 0A0Q in which the
morphism is affine.  Both steps appear here, and the hypotheses carried are theirs.

* Stacks 0415 is `AlgebraicGeometry.Space.isIntegralHom_iff_isAffineHom_and_universallyClosed`.
  It supplies the affineness of `f`, which is what makes `Y` an object of
  `AlgebraicGeometry.Space.AffineOver`, i.e. a candidate for the relative spectrum at all.
* `hint` is the **first assertion of Stacks 0A0Q**, integrality of `f_* 𝒪_Y` over `𝒪_X`.  The
  source derives it from `f` being quasi-compact, quasi-separated and universally closed, and
  that derivation is not available in this library: it needs the comparison between the
  sections of `f_* 𝒪_Y` over an affine étale chart `V` of `X` and the ring of functions on
  `Y ×_X V`.  So it is carried, as it is wherever this library uses 0A0Q, and the universal
  closedness of `f` — the other half of 0415 — is consequently not used.
* `E` is the anti-equivalence of Stacks 081V, which is what `\underline{Spec}_X` means here and
  is not inhabited in this library, and `hqc'` is quasi-coherence of `𝒪'`, the first assertion
  of Stacks 0820.  Both are already the hypotheses of
  `AlgebraicGeometry.Space.normalizationIn`, so they appear for the statement to be about
  anything.

With `f` affine, the content is that the inclusion `𝒪' ⊂ f_* 𝒪_Y` is an isomorphism: a morphism
of algebra sheaves out of an integral one factors through the integral closure of its target
(`AlgebraicGeometry.Space.AlgebraSheaf.existsUnique_hom_integralClosureSheaf`), so the identity
of `f_* 𝒪_Y` does, which splits the inclusion; the inclusion is injective on sections over every
chart, hence a monomorphism, so the splitting is a two-sided inverse.  The anti-equivalence then
carries that isomorphism of algebras to an isomorphism `X' ≅ Y` of algebraic spaces over `X`.

Stacks 0825 is read as an isomorphism over `X` and not as invertibility of the canonical
morphism `Y ⟶ X'` of Stacks 0822: that morphism factors through `\underline{Spec}_X(f_* 𝒪_Y)`
by way of the morphism of Stacks 081X, and no statement identifying *that* morphism with an
isomorphism for an affine `f` is available, the direct-image description of
`AlgebraicGeometry.Space.relativeSpecDirectImageMap` being absent from the library.

## References

* [Stacks Project, Tag 0825](https://stacks.math.columbia.edu/tag/0825)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (E : AffineAlgebraAntiEquivalence B S hS) {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0825.**  The integral closure of `X` in `Y` is `Y`: for an integral morphism
`f : Y ⟶ X` of algebraic spaces whose direct image `f_* 𝒪_Y` is integral over `𝒪_X`, the
normalization `X' ⟶ X` of `X` in `Y` is canonically isomorphic to `Y` over `X`. -/
@[stacks 0825]
def normalizationInIsoOfIsIntegralHom (f : Y ⟶ X) (hf : IsIntegralHom B S hS f.hom)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hint : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegral) :
    (normalizationIn B S hS E f hqc').obj ≅ Over.mk f :=
  have haff : IsAffineHom B S hS (Over.mk f).hom.hom :=
    ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS Y.2 X.2 f.hom).1 hf).1
  haveI hmono : Mono (AlgebraSheaf.integralClosureInclusion
      (pushforwardAlgebra B S hS (Over.mk f))) :=
    ⟨fun g h hgh => AlgebraSheaf.Hom.ext
      ((cancel_mono (AlgebraSheaf.integralClosureInclusion
        (pushforwardAlgebra B S hS (Over.mk f))).right).1
        (by rw [← AlgebraSheaf.comp_right, ← AlgebraSheaf.comp_right, hgh]))⟩
  haveI hiso : IsIso (AlgebraSheaf.integralClosureInclusion
      (pushforwardAlgebra B S hS (Over.mk f))) := by
    obtain ⟨ψ, hψ, -⟩ := AlgebraSheaf.existsUnique_hom_integralClosureSheaf
      (𝟙 (pushforwardAlgebra B S hS (Over.mk f))) hint
    refine ⟨ψ, ?_, hψ⟩
    rw [← cancel_mono (AlgebraSheaf.integralClosureInclusion
      (pushforwardAlgebra B S hS (Over.mk f))), Category.assoc, hψ, Category.comp_id,
      Category.id_comp]
  (ObjectProperty.ι _).mapIso
    (show normalizationIn B S hS E f hqc' ≅ (⟨Over.mk f, haff⟩ : AffineOver B S hS X) from
      Iso.unop
        ((E.equivalence X).unitIso.app (op (⟨Over.mk f, haff⟩ : AffineOver B S hS X)) ≪≫
          (E.equivalence X).inverse.mapIso
            ((E.pushforwardIso X).app (op (⟨Over.mk f, haff⟩ : AffineOver B S hS X)) ≪≫
              ObjectProperty.isoMk
                (P := (AlgebraSheaf.IsQuasicoherent :
                  ObjectProperty (AlgebraSheaf.{u, u} B S hS X.1 X.2)))
                (E.pushforward_obj X ⟨Over.mk f, haff⟩ ≪≫
                  (asIso (AlgebraSheaf.integralClosureInclusion
                    (pushforwardAlgebra B S hS (Over.mk f)))).symm))))

/-- The identification of the normalization of `X` in `Y` with `Y` is over `X`: composing it
with `f` gives the normalization morphism `ν : X' ⟶ X`. -/
theorem normalizationInIsoOfIsIntegralHom_w (f : Y ⟶ X) (hf : IsIntegralHom B S hS f.hom)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hint : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegral) :
    (normalizationInIsoOfIsIntegralHom B S hS E f hf hqc' hint).hom.left ≫ f =
      (normalizationIn B S hS E f hqc').obj.hom :=
  Over.w _

end AlgebraicGeometry.Space

end
