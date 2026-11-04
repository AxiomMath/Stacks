module

public import StacksFrontier.AlgebraicGeometry.Blowup.SectionExtension
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.StrictTransformOpenSubscheme

/-!
# Extending a section of a proper morphism after an admissible blowup, Stacks tag 0CP1

Let `S` be a quasi-compact and quasi-separated scheme, let `U ⊆ W ⊆ S` be quasi-compact opens,
let `f : X ⟶ W` be proper and let `s : U ⟶ X` be a section of `f` over `U`. Then `s` extends to
`b⁻¹(W)` for some `U`-admissible blowup `b : S' ⟶ S`.

The two results [Stacks, Tag 081T] cites are supplied by proved declarations:
[Stacks, Tag 080Y] by `AlgebraicGeometry.cartierBoundaryReduction` and [Stacks, Tag 081S] by
`AlgebraicGeometry.strictTransformOpenImmersion_of_isIso_morphismRestrict`, the latter applied
to the scheme-theoretic image of `s` over `W`, which is proper and, by [Stacks, Tag 0CNG], an
isomorphism over `U`.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_extending_section_of_qcqs`: Stacks tag 0CP1.

## References

* [Stacks Project, Tag 0CP1](https://stacks.math.columbia.edu/tag/0CP1)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 0CNG](https://stacks.math.columbia.edu/tag/0CNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S X : Scheme.{u}}

/-- **Stacks Project, Tag 0CP1.** Let `S` be a quasi-compact and quasi-separated scheme, let
`W ⊆ S` be a quasi-compact open subscheme and let `U ⊆ W` be a quasi-compact open subscheme.
Let `f : X ⟶ W` be proper and let `s : U ⟶ X` satisfy `s ≫ f = U.ι`. Then there is a
`U`-admissible blowup `b : S' ⟶ S` and a morphism `s' : b⁻¹(W) ⟶ X` with `s' ≫ f = b|_{b⁻¹(W)}`
extending `s`, the extension being witnessed by a morphism `t : U ⟶ b⁻¹(W)` over `W`. -/
@[stacks 0CP1 "the conclusion in full, under exactly the source's hypotheses (1)-(3)"]
theorem exists_isAdmissibleBlowup_extending_section_of_qcqs [CompactSpace S]
    [QuasiSeparatedSpace S] (W : S.Opens) (U : W.toScheme.Opens) (hW : IsCompact (W : Set S))
    (hU : IsCompact (U : Set W.toScheme)) (f : X ⟶ W.toScheme) [IsProper f]
    (s : U.toScheme ⟶ X) (hs : s ≫ f = U.ι) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S),
      Stacks.Blowup.IsAdmissibleBlowup (W.ι ''ᵁ U) b ∧
        ∃ s' : (b ⁻¹ᵁ W).toScheme ⟶ X,
          s' ≫ f = b ∣_ W ∧
            ∃ t : U.toScheme ⟶ (b ⁻¹ᵁ W).toScheme, t ≫ b ∣_ W = U.ι ∧ t ≫ s' = s := by
  have : QuasiSeparatedSpace W.toScheme := W.ι.isOpenEmbedding.quasiSeparatedSpace
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  -- The scheme-theoretic image of `s` is an isomorphism onto `W` above `U`.
  have hqIso : IsIso ((s.imageι ≫ f) ∣_ U) := by
    have hpb : IsIso (pullback.snd (s.imageι ≫ f) U.ι) :=
      isIso_pullback_snd_imageι_comp_of_section f U (hU.isRetrocompact U.2) s hs
    refine (isIso_comp_left_iff (pullbackRestrictIsoRestrict (s.imageι ≫ f) U).hom _).mp ?_
    rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
    exact hpb
  exact exists_isAdmissibleBlowup_extending_section W U hW hU f s hs
    (cartierBoundaryReduction U hU)
    (strictTransformOpenImmersion_of_isIso_morphismRestrict (s.imageι ≫ f) U hU)

end AlgebraicGeometry

end
