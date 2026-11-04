module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# Comparisons for the normalization of an algebraic space in another

Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S`
and let `Y ⟶ X' ⟶ X` be the normalization of `X` in `Y` of Definition 0822,
`AlgebraicGeometry.Space.normalizationInQcqsHom` with the factorization
`AlgebraicGeometry.Space.toNormalizationInQcqs`.  Stacks 0ABP asserts:

1. if `W ⟶ X` is étale, then `W ×_X X'` is the normalization of `W` in `W ×_X Y`;
2. if `Y` and `X` are representable, then `X'` is representable and canonically isomorphic to
   the normalization of the scheme `X` in the scheme `Y` (Morphisms, Section 035E).

Both are proved here at exactly these hypotheses.

## Main results

* `AlgebraicGeometry.Space.isIntegrallyClosed_pushforwardAlgebra_toNormalizationInQcqs`: the
  structure sheaf of `X'` is integrally closed in `f'_* 𝒪_Y`.
* `AlgebraicGeometry.Space.isRelativeNormalization_normalizationInQcqs_etaleBaseChange`:
  **part (1) of Stacks 0ABP.**
* `AlgebraicGeometry.Space.isRepresentable_normalizationInQcqs_and_iso_normalization`:
  **part (2) of Stacks 0ABP.**

## Implementation notes

**What "is the normalization" means.**  In part (1) the conclusion is stated in two forms: the
base-changed factorization has the universal property of Stacks 0823,
`AlgebraicGeometry.Space.IsRelativeNormalization`, and — what that characterization amounts to —
it is joined to the normalization of `W` in `W ×_X Y` of Definition 0822 by a unique isomorphism
compatible with both factorizations.  In part (2) the scheme normalization of Stacks 035E is
Mathlib's `AlgebraicGeometry.Scheme.Hom.normalization` of the induced morphism of schemes
`f₀ : Y₀ ⟶ X₀`; it is read in the site as an object `N₀` whose underlying scheme is identified
with it compatibly with both legs, and "canonically isomorphic" is the unique isomorphism
`X' ≅ N₀` compatible with both factorizations.

**Part (1).**  The source's reason is that the construction commutes with étale base change.
The proof here goes through the normalization of `X'` in `Y`, which is `X'` itself by the final
clause of Stacks 0823: so `𝒪_{X'}` is integrally closed in `f'_* 𝒪_Y`, a condition on the
structure map of `f'` alone, which is étale local; see
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInEtaleBaseChange`.

**Part (2).**  The normalization of schemes has the universal property of Stacks 0823 among
algebraic spaces (`AlgebraicGeometry.Space.isRelativeNormalization_yoneda_map_of_normalization`),
so the characterization of Stacks 0823 identifies it with `X'`.

## References

* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 035E](https://stacks.math.columbia.edu/tag/035E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-- **The structure sheaf of the normalization `X'` of `X` in `Y` is integrally closed in
`f'_* 𝒪_Y`.**  By the final clause of Stacks 0823 the identity of `X'` is the normalization of
`X'` in `Y`, and so is the normalization of Stacks 0822 for the quasi-compact quasi-separated
`f' : Y ⟶ X'`, whose algebra is the integral closure. -/
theorem isIntegrallyClosed_pushforwardAlgebra_toNormalizationInQcqs :
    (pushforwardAlgebra B S hS
      (Over.mk (toNormalizationInQcqs f hfqc hfqs))).IsIntegrallyClosed := by
  obtain ⟨hrel, hqc', hqs', -⟩ := isRelativeNormalization_comparison_normalizationInQcqs f hfqc
    hfqs (normalizationInQcqsHom B S hS f hfqc hfqs)
    (isIntegralHom_normalizationInQcqsHom f hfqc hfqs) (toNormalizationInQcqs f hfqc hfqs)
    (toNormalizationInQcqs_comp f hfqc hfqs) (𝟙 _) (Category.comp_id _) (Category.id_comp _)
  let f' := toNormalizationInQcqs f hfqc hfqs
  exact isIntegrallyClosed_of_isRelativeNormalization_id B S hS f' hrel
    (normalizationInQcqsAffineOver B S hS f' hqc' hqs') (toNormalizationInQcqsOver f' hqc' hqs')
    (isRelativeNormalization_normalizationInQcqs f' hqc' hqs')
    (normalizationInQcqsPushforwardIso B S hS f' hqc' hqs').symm (by
      rw [pushforwardAlgebraMap_toNormalizationInQcqsOver]
      exact Iso.inv_hom_id_assoc _ _)

/-- **Stacks 0ABP, part (1).**  Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism
of algebraic spaces over `S`, with normalization `Y ⟶ X' ⟶ X` (Definition 0822), and let
`g : W ⟶ X` be étale.  Let `P = W ×_X X'` and `Y' = W ×_X Y`, with `f'_P : Y' ⟶ P` the base
change of `f' : Y ⟶ X'`.  Then `Y' ⟶ P ⟶ W` is the normalization of `W` in `Y'`: it has the
universal property of Stacks 0823, and it is joined to the normalization of `W` in `Y'` of
Definition 0822 by a unique isomorphism compatible with both factorizations. -/
@[stacks 0ABP "part (1): for W ⟶ X étale, W ×_X X' is the normalization of W in W ×_X Y"]
theorem isRelativeNormalization_normalizationInQcqs_etaleBaseChange
    {W P Y' : AlgebraicSpaces B S hS} (g : W ⟶ X) (hg : IsEtale B S hS g.hom)
    (i : P ⟶ normalizationInQcqs B S hS f hfqc hfqs) (νP : P ⟶ W)
    (hP : IsPullback i νP (normalizationInQcqsHom B S hS f hfqc hfqs) g)
    (j : Y' ⟶ Y) (fW : Y' ⟶ W) (hY : IsPullback j fW f g) (f'P : Y' ⟶ P)
    (h₁ : f'P ≫ i = j ≫ toNormalizationInQcqs f hfqc hfqs) (h₂ : f'P ≫ νP = fW) :
    IsRelativeNormalization B S hS fW.hom νP.hom f'P.hom ∧
      ∃ (hWqc : IsQuasiCompact B S hS fW.hom) (hWqs : IsQuasiSeparated B S hS fW.hom),
        ∃! e : (normalizationInQcqs B S hS fW hWqc hWqs).1 ≅ P.1,
          (toNormalizationInQcqs fW hWqc hWqs).hom ≫ e.hom = f'P.hom ∧
            e.hom ≫ νP.hom = (normalizationInQcqsHom B S hS fW hWqc hWqs).hom := by
  have hout : IsPullback j (f'P ≫ νP) (toNormalizationInQcqs f hfqc hfqs ≫
      normalizationInQcqsHom B S hS f hfqc hfqs) g := by
    rw [h₂, toNormalizationInQcqs_comp]
    exact hY
  have hsq : IsPullback j f'P (toNormalizationInQcqs f hfqc hfqs) i :=
    IsPullback.of_bot hout h₁.symm hP
  have hrel := isRelativeNormalization_of_isPullback_of_isEtale B S hS
    (toNormalizationInQcqs f hfqc hfqs) (normalizationInQcqsHom B S hS f hfqc hfqs)
    (isIntegralHom_normalizationInQcqsHom f hfqc hfqs)
    (isIntegrallyClosed_pushforwardAlgebra_toNormalizationInQcqs f hfqc hfqs) g hg i νP hP j f'P
    hsq
  rw [h₂] at hrel
  have hYp : IsPullback j.hom fW.hom f.hom g.hom := hY.map (ObjectProperty.ι _)
  have hWqc : IsQuasiCompact B S hS fW.hom := isQuasiCompact_of_isPullback B S hS hYp hfqc
  have hWqs : IsQuasiSeparated B S hS fW.hom := isQuasiSeparated_of_isPullback B S hS hYp hfqs
  exact ⟨hrel, hWqc, hWqs,
    existsUnique_iso_normalizationInQcqs_of_isRelativeNormalization fW hWqc hWqs P.2 hrel⟩

include hfqc hfqs in
/-- A morphism of the site representing, through isomorphisms, a quasi-compact and
quasi-separated morphism of algebraic spaces is quasi-compact and quasi-separated as a morphism
of schemes. -/
theorem quasiCompact_quasiSeparated_toScheme_map_of_iso {X₀ Y₀ : BigFppfOver B S hS}
    (eX : X.1 ≅ yoneda.obj X₀) (eY : Y.1 ≅ yoneda.obj Y₀) (f₀ : Y₀ ⟶ X₀)
    (hf₀ : yoneda.map f₀ = eY.inv ≫ f.hom ≫ eX.hom) :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀) ∧
      QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀) := by
  have hsq : IsPullback eY.inv (yoneda.map f₀) f.hom eX.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [hf₀]; simp⟩
  have hqc : IsQuasiCompact B S hS (yoneda.map f₀) := isQuasiCompact_of_isPullback B S hS hsq hfqc
  have hqs : IsQuasiSeparated B S hS (yoneda.map f₀) :=
    isQuasiSeparated_of_isPullback B S hS hsq hfqs
  refine ⟨?_, (isQuasiSeparated_yoneda_map_iff B S hS f₀).1 hqs⟩
  exact MorphismProperty.of_relative_map (F := yoneda)
    (P := MorphismProperty.inverseImage (@QuasiCompact.{u}) (BigFppfOver.toScheme B S hS))
    (presheaf_quasiCompact_of_isQuasiCompact B S hS
      (Functor.relativelyRepresentable.map yoneda f₀) hqc)

/-- **Stacks 0ABP, part (2).**  Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism
of algebraic spaces over `S` with `X` and `Y` representable, by objects `X₀` and `Y₀` of the
site, and let `f₀ : Y₀ ⟶ X₀` be the induced morphism.  Then the normalization `X'` of `X` in `Y`
(Definition 0822) is representable, and canonically isomorphic to the normalization of the scheme
`X₀` in the scheme `Y₀` (Morphisms, Section 035E): there is an object `N₀` of the site whose
underlying scheme is that normalization, compatibly with both of its legs, and a unique
isomorphism `X' ≅ N₀` compatible with both factorizations. -/
@[stacks 0ABP "part (2): for X and Y representable, X' is representable and canonically
  isomorphic to the normalization of the scheme X in the scheme Y of 035E"]
theorem isRepresentable_normalizationInQcqs_and_iso_normalization {X₀ Y₀ : BigFppfOver B S hS}
    (eX : X.1 ≅ yoneda.obj X₀) (eY : Y.1 ≅ yoneda.obj Y₀) (f₀ : Y₀ ⟶ X₀)
    (hf₀ : yoneda.map f₀ = eY.inv ≫ f.hom ≫ eX.hom) :
    (normalizationInQcqs B S hS f hfqc hfqs).1.IsRepresentable ∧
      ∃ (_ : QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀))
        (_ : QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀))
        (N₀ : BigFppfOver B S hS) (t : Y₀ ⟶ N₀) (ν₀ : N₀ ⟶ X₀)
        (e : (BigFppfOver.toScheme B S hS).obj N₀ ≅
          ((BigFppfOver.toScheme B S hS).map f₀).normalization),
        (BigFppfOver.toScheme B S hS).map t ≫ e.hom =
            ((BigFppfOver.toScheme B S hS).map f₀).toNormalization ∧
          e.hom ≫ ((BigFppfOver.toScheme B S hS).map f₀).fromNormalization =
            (BigFppfOver.toScheme B S hS).map ν₀ ∧
          ∃! φ : (normalizationInQcqs B S hS f hfqc hfqs).1 ≅ yoneda.obj N₀,
            (toNormalizationInQcqs f hfqc hfqs).hom ≫ φ.hom = eY.hom ≫ yoneda.map t ∧
              φ.hom ≫ yoneda.map ν₀ = (normalizationInQcqsHom B S hS f hfqc hfqs).hom ≫ eX.hom := by
  obtain ⟨hqc₀, hqs₀⟩ := quasiCompact_quasiSeparated_toScheme_map_of_iso f hfqc hfqs eX eY f₀ hf₀
  have hrel := isRelativeNormalization_normalizationInQcqs f hfqc hfqs
  obtain ⟨N₀, t, ν₀, e, φ, hφ1, hφ2, ht, hν⟩ :=
    hrel.exists_iso_normalization_of_representable
      (normalizationInQcqs B S hS f hfqc hfqs).2 eX eY f₀ hf₀
  refine ⟨Functor.IsRepresentable.mk' φ.symm, hqc₀, hqs₀, N₀, t, ν₀, e, ht, hν, φ, ⟨hφ1, hφ2⟩, ?_⟩
  rintro ψ ⟨hψ1, hψ2⟩
  -- both `φ` and `ψ` are isomorphisms between relative normalizations of `yoneda.map f₀`
  have hN := isRelativeNormalization_yoneda_map_of_normalization B S hS f₀ t ν₀ e ht hν
  have h' := hrel.ofIso eY eX
  rw [← hf₀] at h'
  obtain ⟨χ, -, hχu⟩ := h'.existsUnique_iso hN (normalizationInQcqs B S hS f hfqc hfqs).2
    (isAlgebraicSpace_yoneda B S hS N₀)
  have key : ∀ θ : (normalizationInQcqs B S hS f hfqc hfqs).1 ≅ yoneda.obj N₀,
      (toNormalizationInQcqs f hfqc hfqs).hom ≫ θ.hom = eY.hom ≫ yoneda.map t →
      θ.hom ≫ yoneda.map ν₀ = (normalizationInQcqsHom B S hS f hfqc hfqs).hom ≫ eX.hom →
      θ = χ := fun θ h1 h2 => hχu θ ⟨by rw [Category.assoc, h1, Iso.inv_hom_id_assoc], h2⟩
  exact (key ψ hψ1 hψ2).trans (key φ hφ1 hφ2).symm

end AlgebraicGeometry.Space

end
