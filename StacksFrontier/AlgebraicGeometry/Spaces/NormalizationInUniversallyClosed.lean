module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverPushforwardReflectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsUniversalProperty

/-!
# The normalization of `Y` in a universally closed `X` is `\underline{Spec}_Y(f_*𝒪_X)`

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and universally closed morphism of algebraic
spaces over `S`.  Stacks 0A0Q asserts that `f_*𝒪_X` is integral over `𝒪_Y` — proved in
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions` — and, in other words,
that the normalization `X ⟶ Y' ⟶ Y` of `Y` in `X` (Stacks 0822) is the factorization
`X ⟶ \underline{Spec}_Y(f_*𝒪_X) ⟶ Y` of Stacks 081X.  This file proves the second sentence.

The factorization of Stacks 081X is the morphism `X ⟶ \underline{Spec}_Y(f_*𝒪_X)` over `Y`
whose induced map on direct-image algebras is the identity of `f_*𝒪_X`; that is, it is a
factorization `X ⟶ Z ⟶ Y` of `f` through an algebraic space `Z` affine over `Y` such that the
map `(Z ⟶ Y)_*𝒪_Z ⟶ f_*𝒪_X` it induces is an isomorphism of `𝒪_Y`-algebras.  Such a
factorization is unique up to unique isomorphism
(`AlgebraicGeometry.Space.existsUnique_iso_of_isIso_pushforwardAlgebraMap`), so "the
normalization of `Y` in `X` is the factorization of Stacks 081X" is the conjunction of:

* the normalization `ν : Y' ⟶ Y` is affine (part of Stacks 0822), and the map
  `ν_*𝒪_{Y'} ⟶ f_*𝒪_X` induced by the canonical `f' : X ⟶ Y'` is an isomorphism; and
* consequently every factorization of Stacks 081X type is uniquely isomorphic to the
  normalization, compatibly with the factorizations.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `isIso_pushforwardAlgebraMap_of_universallyClosed`: for universally closed `f`, a
  factorization of `f` whose algebra is the integral closure `𝒪'`, the factorization inducing the
  inclusion `𝒪' ⊂ f_*𝒪_X`, induces an isomorphism of algebras.
* `existsUnique_iso_of_isIso_pushforwardAlgebraMap`: two factorizations through algebraic spaces
  affine over `Y` inducing isomorphisms of direct-image algebras are related by a unique
  isomorphism over `Y`.
* `isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed` and
  `existsUnique_iso_normalizationInQcqs_of_universallyClosed`:
  **Stacks 0A0Q, second sentence.**

## References

* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Let `ν : Y' ⟶ Y` be a morphism of algebraic spaces, `h : X ⟶ Y'` a factorization of
`f : X ⟶ Y` through it, and `e : ν_*𝒪_{Y'} ≅ 𝒪'` an identification of the direct image of
`𝒪_{Y'}` with the integral closure `𝒪'` of `𝒪_Y` in `f_*𝒪_X` under which the map
`h^♯ : ν_*𝒪_{Y'} ⟶ f_*𝒪_X` induced by `h` is the inclusion `𝒪' ⊂ f_*𝒪_X`.  If `f` is
universally closed then `h^♯` is an isomorphism of `𝒪_Y`-algebras: `f_*𝒪_X` is integral, so
`𝒪' = f_*𝒪_X`. -/
theorem isIso_pushforwardAlgebraMap_of_universallyClosed (f : X ⟶ Y)
    (huc : UniversallyClosed B S hS f.hom) {ν : Over Y} (h : Over.mk f ⟶ ν)
    (e : pushforwardAlgebra B S hS ν ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)))
    (he : pushforwardAlgebraMap B S hS h =
      e.hom ≫ AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk f))) :
    IsIso (pushforwardAlgebraMap B S hS h) := by
  have := isIso_integralClosureInclusion_pushforwardAlgebra_of_universallyClosed B S hS f huc
  rw [he]
  infer_instance

/-- **The factorization of Stacks 081X is unique up to unique isomorphism.**  Two factorizations
`T ⟶ Z₁ ⟶ Y` and `T ⟶ Z₂ ⟶ Y` of a morphism of algebraic spaces through algebraic spaces affine
over `Y`, each inducing an isomorphism of direct-image algebras `(Zᵢ ⟶ Y)_*𝒪 ≅ T_*𝒪`, are
related by a unique isomorphism `Z₁ ≅ Z₂` over `Y` compatible with the two factorizations. -/
theorem existsUnique_iso_of_isIso_pushforwardAlgebraMap {T : Over Y}
    (Z₁ Z₂ : AffineOver B S hS Y) (g₁ : T ⟶ Z₁.obj) (g₂ : T ⟶ Z₂.obj)
    [IsIso (pushforwardAlgebraMap B S hS g₁)] [IsIso (pushforwardAlgebraMap B S hS g₂)] :
    ∃! k : Z₁.obj ≅ Z₂.obj, g₁ ≫ k.hom = g₂ := by
  obtain ⟨k, hk⟩ := exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS
    (relativelyRepresentable_of_isAffineHom B S hS Z₁.obj.hom Z₁.property) Z₂
    (pushforwardAlgebraMap B S hS g₂ ≫ inv (pushforwardAlgebraMap B S hS g₁))
  have hfac : g₁ ≫ k = g₂ := eq_of_pushforwardAlgebraMap_eq B S hS Z₂ (by
    rw [pushforwardAlgebraMap_comp, hk, Category.assoc, IsIso.inv_hom_id, Category.comp_id])
  have : IsIso (pushforwardAlgebraMap B S hS k) := by rw [hk]; infer_instance
  have : IsIso k := isIso_of_isIso_pushforwardAlgebraMap B S hS Z₁ Z₂ k
  refine ⟨asIso k, hfac, fun k' hk' => Iso.ext ?_⟩
  refine eq_of_pushforwardAlgebraMap_eq B S hS Z₂ ?_
  rw [asIso_hom, hk, IsIso.eq_comp_inv, ← pushforwardAlgebraMap_comp, hk']

/-! ### Stacks 0A0Q, second sentence -/

section Normalization

variable {B S hS} (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (huc : UniversallyClosed B S hS f.hom)

include huc in
/-- **Stacks 0A0Q, second sentence: the normalization of `Y` in `X` is
`\underline{Spec}_Y(f_*𝒪_X)`.**  Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and
universally closed morphism of algebraic spaces, and let `X ⟶ Y' ⟶ Y` be the normalization of
`Y` in `X` (Stacks 0822; `ν : Y' ⟶ Y` is affine).  Then the map `ν_*𝒪_{Y'} ⟶ f_*𝒪_X` of
`𝒪_Y`-algebras induced by the canonical morphism `f' : X ⟶ Y'` is an isomorphism, so
`Y' = \underline{Spec}_Y(f_*𝒪_X)` and `f'` is the canonical morphism of Stacks 081X.

The map induced by `f'` is `ν_*𝒪_{Y'} ≅ 𝒪' ⊂ f_*𝒪_X`
(`AlgebraicGeometry.Space.pushforwardAlgebraMap_toNormalizationInQcqsOver`), and the inclusion
of the integral closure `𝒪'` is all of `f_*𝒪_X` because `f_*𝒪_X` is integral over `𝒪_Y`, the
first sentence of the tag. -/
@[stacks 0A0Q "second sentence: the normalization X ⟶ Y' ⟶ Y of Y in X induces \
ν_*O_{Y'} ≅ f_*O_X, i.e. Y' = Spec_Y(f_*O_X) with the factorization of 081X"]
theorem isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed :
    IsIso (pushforwardAlgebraMap B S hS (toNormalizationInQcqsOver f hfqc hfqs)) :=
  isIso_pushforwardAlgebraMap_of_universallyClosed B S hS f huc _
    (normalizationInQcqsPushforwardIso B S hS f hfqc hfqs)
    (pushforwardAlgebraMap_toNormalizationInQcqsOver f hfqc hfqs)

include huc in
/-- **Stacks 0A0Q, second sentence, as an identification of factorizations.**  For a
quasi-compact, quasi-separated and universally closed `f : X ⟶ Y`, every factorization
`X ⟶ Z ⟶ Y` of `f` of the kind Stacks 081X constructs — `Z` affine over `Y` and the induced map
`(Z ⟶ Y)_*𝒪_Z ⟶ f_*𝒪_X` an isomorphism, i.e. `Z = \underline{Spec}_Y(f_*𝒪_X)` with its
canonical morphism from `X` — is the normalization of `Y` in `X`: there is a unique isomorphism
`Y' ≅ Z` over `Y` from the normalization carrying the canonical `f' : X ⟶ Y'` to `X ⟶ Z`. -/
@[stacks 0A0Q "second sentence: the normalization of Y in X is, uniquely, the factorization \
X ⟶ Spec_Y(f_*O_X) ⟶ Y of 081X"]
theorem existsUnique_iso_normalizationInQcqs_of_universallyClosed
    (Z : AffineOver B S hS Y) (g : Over.mk f ⟶ Z.obj)
    [IsIso (pushforwardAlgebraMap B S hS g)] :
    ∃! k : (normalizationInQcqsAffineOver B S hS f hfqc hfqs).obj ≅ Z.obj,
      toNormalizationInQcqsOver f hfqc hfqs ≫ k.hom = g :=
  have := isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed f hfqc
    hfqs huc
  existsUnique_iso_of_isIso_pushforwardAlgebraMap B S hS _ Z _ g

end Normalization

end AlgebraicGeometry.Space

end
