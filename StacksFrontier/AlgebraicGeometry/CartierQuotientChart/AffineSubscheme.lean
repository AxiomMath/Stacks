module

public import StacksFrontier.AlgebraicGeometry.CartierQuotientChart.Basic

/-!
# The closed subscheme of an affine scheme cut out by an ideal of global functions

Let `X` be an affine scheme with `R = Γ(X, ⊤)` and let `I : X.IdealSheafData`. The closed
subscheme `I.subscheme` is then the spectrum of `R / I(⊤)`, compatibly with the two closed
immersions into `X ≅ Spec R`. In particular, for an ideal `J` of `R` the closed subscheme cut out
by `AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop J` is `Spec (R / J)`, since the ideal of
`ofIdealTop J` at `⊤` is `J`.

When `X` is affine, the open `V = ⊤` is one of the affine charts of `I.subscheme`, and the
chart `Stacks.CartierQuotientChart.quotientChart` at `⊤` is a global identification.

## Main definitions

* `Stacks.CartierQuotientChart.topChart`: the fibre product of `I.subscheme` with `⊤` is
  `I.subscheme`.
* `Stacks.CartierQuotientChart.subschemeIsoSpecQuotient`: the isomorphism
  `I.subscheme ≅ Spec (Γ(X, ⊤) ⧸ I(⊤))` for affine `X`.

## Main results

* `Stacks.CartierQuotientChart.subschemeIsoSpecQuotient_hom_comp`: the isomorphism is compatible
  with the closed immersions into `Spec Γ(X, ⊤)`.
* `Stacks.CartierQuotientChart.exists_subschemeIsoSpec_of_ideal_eq`: if `I(⊤) = K`, then
  `I.subscheme ≅ Spec (Γ(X, ⊤) ⧸ K)`, compatibly with the closed immersions into
  `Spec Γ(X, ⊤)`.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CartierQuotientChart

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The inverse of `AlgebraicGeometry.Scheme.topIso` followed by the inclusion of `⊤` is the
identity. -/
private theorem topIso_inv_comp_top_ι : (Scheme.topIso X).inv ≫ (⊤ : X.Opens).ι = 𝟙 X :=
  Iso.inv_hom_id _

/-- The identity of `I.subscheme` has the same range as the inclusion of the preimage of `⊤`
under the closed immersion `I.subschemeι`. -/
theorem range_id_subscheme :
    Set.range (𝟙 I.subscheme : I.subscheme ⟶ I.subscheme) =
      Set.range (I.subschemeι ⁻¹ᵁ (⊤ : X.Opens)).ι := by
  rw [Scheme.Opens.range_ι, Scheme.Hom.preimage_top]
  simp

/-- The fibre product of the closed subscheme with the open `⊤` is the closed subscheme. -/
def topChart : pullback I.subschemeι (⊤ : X.Opens).ι ≅ I.subscheme :=
  @chartOfCover X I ⊤ _ (𝟙 I.subscheme) inferInstance (range_id_subscheme I)

/-- The projection of the fibre product over `⊤` down to `⊤`, read through
`AlgebraicGeometry.Scheme.topIso`, is the closed immersion. -/
theorem id_subschemeι_comp :
    (I.subschemeι ≫ (Scheme.topIso X).inv) ≫ (⊤ : X.Opens).ι =
      (𝟙 I.subscheme) ≫ I.subschemeι := by
  rw [Category.assoc, topIso_inv_comp_top_ι, Category.comp_id, Category.id_comp]

/-- Composing `topChart` with the closed immersion `I.subschemeι`, read into `⊤` through
`AlgebraicGeometry.Scheme.topIso`, gives the second projection of the fibre product. -/
theorem topChart_hom_comp :
    (topChart I).hom ≫ (I.subschemeι ≫ (Scheme.topIso X).inv) =
      pullback.snd I.subschemeι (⊤ : X.Opens).ι :=
  @chartOfCover_hom_comp X I ⊤ _ (𝟙 I.subscheme) inferInstance (range_id_subscheme I)
    (I.subschemeι ≫ (Scheme.topIso X).inv) (id_subschemeι_comp I)

/-- Comparing an affine scheme with the spectrum of its global functions is the same as comparing
the open `⊤` with it. -/
theorem topIso_inv_isoSpec_hom [IsAffine X] :
    (Scheme.topIso X).inv ≫ (isAffineOpen_top X).isoSpec.hom = X.isoSpec.hom := by
  rw [AlgebraicGeometry.IsAffineOpen.isoSpec_hom, AlgebraicGeometry.Scheme.Opens.toSpecΓ_top,
    Scheme.isoSpec_hom, ← Category.assoc, topIso_inv_comp_top_ι, Category.id_comp]

/-- **The closed subscheme of an affine scheme is the spectrum of a quotient of its global
functions.** -/
def subschemeIsoSpecQuotient [IsAffine X] :
    I.subscheme ≅ Spec (.of (Γ(X, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top X⟩)) :=
  (topChart I).symm ≪≫ quotientChart I ⟨⊤, isAffineOpen_top X⟩

/-- The identification of `I.subscheme` with `Spec (Γ(X, ⊤) ⧸ I(⊤))` carries the closed immersion
of `I.subscheme` into `X ≅ Spec Γ(X, ⊤)` to the closed immersion of the spectrum of the
quotient. -/
theorem subschemeIsoSpecQuotient_hom_comp [IsAffine X] :
    (subschemeIsoSpecQuotient I).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩))) =
      I.subschemeι ≫ X.isoSpec.hom := by
  rw [subschemeIsoSpecQuotient, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← quotientChart_hom_comp I ⟨⊤, isAffineOpen_top X⟩, ← topChart_hom_comp I, Category.assoc,
    Iso.inv_hom_id_assoc, Category.assoc, topIso_inv_isoSpec_hom]

/-- **The closed subscheme of an affine scheme cut out by a known ideal of global functions is
the spectrum of the quotient by it**, compatibly with the closed immersions into
`Spec Γ(X, ⊤)`. -/
theorem exists_subschemeIsoSpec_of_ideal_eq [IsAffine X] {K : Ideal Γ(X, ⊤)}
    (hK : I.ideal ⟨⊤, isAffineOpen_top X⟩ = K) :
    ∃ e : I.subscheme ≅ Spec (.of (Γ(X, ⊤) ⧸ K)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) =
        I.subschemeι ≫ X.isoSpec.hom := by
  subst hK
  exact ⟨subschemeIsoSpecQuotient I, subschemeIsoSpecQuotient_hom_comp I⟩

end Stacks.CartierQuotientChart

end
