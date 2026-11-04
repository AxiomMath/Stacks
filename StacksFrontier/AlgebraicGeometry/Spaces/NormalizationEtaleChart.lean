module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction

/-!
# The normalization of a chart, and functoriality for a representable morphism

Two consequences of the chart condition of `AlgebraicGeometry.Space.NormalizationData` are
drawn here: part (4) of Tag 07U4 for a surjective étale chart by an object of the site, and
part (3) of the same tag for a morphism of the site. Both are restricted against the source
statement, and the restrictions are recorded below.

Let `F` be an algebraic space over `S` equipped with normalization data
`AlgebraicGeometry.Space.NormalizationData`, and let `f : U ⟶ F` be a surjective étale chart of
`F` by an object `U` of the big fppf site of `S`. Tag 07U4, part (4), asserts of an étale
morphism `X ⟶ Y` of algebraic spaces that the induced morphism of normalizations identifies
`X^ν` with `X ×_Y Y^ν`. For `X = U` representable and `f` surjective that assertion is proved
here: the normalization of `U` — presented through any normalization data for the algebraic
space `U` represents — is isomorphic over `U` to the fibre product of the normalization
morphism of `F` with `f`.

The isomorphism is assembled from the two chart conditions. The chart condition of the
normalization data of `F`, read at `f`, already *says* that the fibre product is represented by
an object `Uν` of the site whose underlying scheme is the normalization scheme of the underlying
scheme of `U`. The chart condition of the normalization data of `U`, read at the identity chart,
says the same of `U^ν`. The two objects are therefore isomorphic on underlying schemes over the
underlying scheme of `U`, and the comparison is put back into the site by
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`, whose compatibility hypothesis is
`AlgebraicGeometry.toScheme_map_comp_inclusion_hom`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_yoneda`: condition (2) of Tag
  0BB1 for a representable algebraic space is the same condition on the representing scheme.
* `AlgebraicGeometry.Space.NormalizationData.exists_iso_pullback_of_chart`: for a surjective
  étale chart of an algebraic space with normalization data, the normalization of the chart is
  the fibre product of the normalization morphism with the chart.
* `AlgebraicGeometry.Space.NormalizationData.existsUnique_hom_of_representable`: a morphism of
  the site carrying generic points to generic points induces a unique morphism of the
  normalizations of the algebraic spaces its source and target represent.

## Implementation notes

**The two finiteness proofs.** The chart condition binds the hypothesis needed to form the
normalization of a chart existentially, so the two chart conditions produce two proofs `hU` and
`hU'` of the *same* proposition about the underlying scheme of `U`. They are therefore equal by
proof irrelevance, and `AlgebraicGeometry.Scheme.normalizationScheme` formed with either is the
same scheme definitionally; no transport along an equality of schemes is needed, and the two
comparison isomorphisms compose directly.

**Why this is not part (4).** Part (4) is stated for an arbitrary étale — or smooth — morphism
`X ⟶ Y` of algebraic spaces, and it asserts in addition that the hypotheses of part (3) hold.
What is proved here is the isomorphism for a *representable* `X` and a *surjective* morphism.
Both restrictions are exactly the reach of the chart condition, which quantifies over surjective
étale charts by objects of the site: for a non-surjective étale `U ⟶ F` the chart condition says
nothing about `U`, and for a non-representable `X` the comparison would have to be descended
along an atlas of `X`. Accordingly nothing here carries `@[stacks 07U4]`.

**Why this is not part (3).** Part (3) is stated for a morphism of arbitrary algebraic spaces
satisfying the conditions of Tag 0BB1. What is proved here is the existence and uniqueness of
`φ^ν` for a morphism `φ` of the *site*, that is for a representable morphism of representable
algebraic spaces. The source reduces the general case to this one by choosing surjective étale
charts `U ⟶ X` and `V ⟶ Y` through which the morphism lifts to a morphism `U ⟶ V` of schemes,
and then descending the induced morphism of normalizations along `U^ν ⟶ X^ν`; neither the
chart refinement nor that descent is carried out here. Accordingly this result, too, carries no
tag.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (2) of Tag 0BB1 for a representable algebraic space.** If every quasi-compact
open of the underlying scheme of an object `U` of the big fppf site of `S` has finitely many
irreducible components, then the same holds for every étale scheme chart of the algebraic space
`U` represents.

An étale chart of a representable presheaf is represented by a morphism of the site whose
underlying morphism of schemes is étale, hence smooth, and finiteness of the irreducible
components of the quasi-compact opens ascends along a smooth morphism by
`AlgebraicGeometry.finite_irreducibleComponents_of_smooth`. -/
theorem hasLocallyFiniteIrreducibleComponents_yoneda (U : BigFppfOver B S hS)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    HasLocallyFiniteIrreducibleComponents B S hS (yoneda.obj U) := by
  intro W g hg
  obtain ⟨φ, rfl⟩ : ∃ φ : W ⟶ U, yoneda.map φ = g :=
    ⟨yoneda.preimage g, yoneda.map_preimage g⟩
  have hetale : Etale ((BigFppfOver.toScheme B S hS).map φ) :=
    etale_of_isEtale_yoneda_map B S hS hg
  exact finite_irreducibleComponents_of_smooth ((BigFppfOver.toScheme B S hS).map φ) hU

namespace NormalizationData

variable {B S hS}

/-- **Tag 07U4, part (4), for a surjective étale chart by an object of the site.** Let `D` be
normalization data for an algebraic space `F` over `S`, let `f : U ⟶ F` be a surjective étale
chart of `F` by an object of the big fppf site of `S`, and let `D'` be normalization data for
the algebraic space `U` represents. Then `D'.space` is isomorphic over `U` to the fibre product
of the normalization morphism `D.hom` with `f`.

Both chart conditions present a normalization of the underlying scheme of `U`: `D.chart` at `f`
presents the fibre product as an object `Uν` of the site with an isomorphism of its underlying
scheme onto that normalization, and `D'.chart_self` presents `D'.space` as an object `Uν'` with
an isomorphism onto the same normalization. The composite isomorphism of underlying schemes
commutes with the two morphisms down to `U`, so
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq` lifts it to a morphism `Uν' ⟶ Uν` of the
site; it is an isomorphism because the functor to schemes is fully faithful onto the morphisms
over `S`, and it is the required comparison because the Cartesian square of `D.chart`
identifies `yoneda.obj Uν` with the fibre product.

It does **not** carry `@[stacks 07U4]`; see the implementation notes of this module for the two
restrictions against the source statement of part (4). -/
theorem exists_iso_pullback_of_chart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : NormalizationData B S hS F) {U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ F) (hf : IsSurjective B S hS f) (hfe : IsEtale B S hS f)
    (D' : NormalizationData B S hS (yoneda.obj U)) :
    ∃ φ : D'.space ≅ pullback D.hom f, φ.hom ≫ pullback.snd D.hom f = D'.hom := by
  set T := BigFppfOver.toScheme B S hS
  obtain ⟨hU, Uν, p, g, e, hp, hpb⟩ := D.chart U f hf hfe
  obtain ⟨hU', Uν', p', g', e', hp', hpb'⟩ := D'.chart_self
  have hg' : IsIso g' := hpb'.isIso_fst_of_isIso
  -- The comparison of the two normalized charts, on underlying schemes.
  set φ₀ : T.obj Uν' ⟶ T.obj Uν := e'.hom ≫ e.inv with hφ₀
  have hφ₀p : φ₀ ≫ T.map p = T.map p' := by
    rw [hφ₀, hp, hp', Category.assoc, Iso.inv_hom_id_assoc]
  have hcomp : φ₀ ≫ B.inclusion.map Uν.hom = B.inclusion.map Uν'.hom := by
    rw [← toScheme_map_comp_inclusion_hom B S hS p,
      ← toScheme_map_comp_inclusion_hom B S hS p', ← Category.assoc, hφ₀p]
  obtain ⟨ψ, hψ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS φ₀ hcomp
  -- The functor to schemes reflects isomorphisms, so `ψ` is one.
  have hψiso : IsIso (T.map ψ) := by
    rw [hψ, hφ₀]
    infer_instance
  have h₁ : IsIso (B.inclusion.map ((BigFppfOver.forget B S hS).map ψ)) := hψiso
  have h₂ : IsIso ((BigFppfOver.forget B S hS).map ψ) := isIso_of_reflects_iso _ B.inclusion
  have h₃ : IsIso ψ := isIso_of_reflects_iso _ (Over.forget (B.obj hS))
  have hψp : ψ ≫ p = p' := T.map_injective (by rw [Functor.map_comp, hψ, hφ₀p])
  refine ⟨(asIso g').symm ≪≫ asIso (yoneda.map ψ) ≪≫ hpb.isoPullback, ?_⟩
  have hD' : D'.hom = inv g' ≫ yoneda.map p' := by
    rw [← cancel_epi g', IsIso.hom_inv_id_assoc]
    simpa only [Category.comp_id] using hpb'.w
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
    hpb.isoPullback_hom_snd, hD']
  rw [← Functor.map_comp, hψp]

/-- **Tag 07U4, part (3), for representable algebraic spaces.** Let `φ : X ⟶ Y` be a morphism
of the big fppf site of `S` which carries every generic point of an irreducible component of
the underlying scheme of `X` to a generic point of an irreducible component of the underlying
scheme of `Y`, and let `DX` and `DY` be normalization data for the algebraic spaces `X` and `Y`
represent. Then there is a *unique* morphism `DX.space ⟶ DY.space` of algebraic spaces over `S`
compatible with the two normalization morphisms and with `φ`.

This is `φ^ν` for a representable morphism. The generic-point hypothesis is the membership of
`φ` in the category `C` of the source's proof, which for schemes is the condition of part (3)
that every codimension `0` point of `X` be carried to a codimension `0` point of `Y`.

The construction is Stacks 035Q, part (4), applied to the composite `X^ν ⟶ X ⟶ Y`: its source
is a normal scheme and the composite carries generic points to generic points, because the
normalization morphism does (`AlgebraicGeometry.Scheme.normalization_mem_genericPoints`) and
`φ` does by hypothesis. The resulting morphism of normalization schemes is transported to the
two normalized charts of `DX` and `DY` along the comparison isomorphisms of their chart
conditions, lifted into the site by
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`, and conjugated by the two chart
isomorphisms. Uniqueness travels back along the same three steps, using that the Yoneda
embedding and the functor from the site to schemes are both faithful.

It does **not** carry `@[stacks 07U4]`: part (3) is stated for a morphism of arbitrary
algebraic spaces, and promoting this to that generality needs a common étale refinement of
charts of `X` and `Y` through which the morphism lifts, together with descent of the resulting
morphism of normalizations along the chart — neither of which is available here. -/
theorem existsUnique_hom_of_representable {X Y : BigFppfOver B S hS} (φ : X ⟶ Y)
    (DX : NormalizationData B S hS (yoneda.obj X))
    (DY : NormalizationData B S hS (yoneda.obj Y))
    (hφ : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj X),
      (BigFppfOver.toScheme B S hS).map φ η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj Y)) :
    ∃! h : DX.space ⟶ DY.space, h ≫ DY.hom = DX.hom ≫ yoneda.map φ := by
  obtain ⟨hX, Xν, pX, gX, eX, hpX, hpbX⟩ := DX.chart_self
  obtain ⟨hY, Yν, pY, gY, eY, hpY, hpbY⟩ := DY.chart_self
  have hgX : IsIso gX := hpbX.isIso_fst_of_isIso
  have hgY : IsIso gY := hpbY.isIso_fst_of_isIso
  have hwX : gX ≫ DX.hom = yoneda.map pX := by simpa using hpbX.w
  have hwY : gY ≫ DY.hom = yoneda.map pY := by simpa using hpbY.w
  -- Stacks 035Q, part (4), applied to the composite `X^ν ⟶ X ⟶ Y`.
  have hnormal : _root_.AlgebraicGeometry.IsNormal
      (Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj X) hX) :=
    Scheme.isNormal_normalizationScheme _ hX
  have hgen : ∀ η : genericPoints
      (Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj X) hX),
      (((BigFppfOver.toScheme B S hS).obj X).normalization hX ≫
          (BigFppfOver.toScheme B S hS).map φ) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj Y) :=
    fun η => hφ ⟨_, Scheme.normalization_mem_genericPoints
      ((BigFppfOver.toScheme B S hS).obj X) hX η.2⟩
  obtain ⟨σ, hσ, hσu⟩ := Scheme.existsUnique_lift_normalization hY
    (((BigFppfOver.toScheme B S hS).obj X).normalization hX ≫
      (BigFppfOver.toScheme B S hS).map φ) hgen
  -- Transport `σ` to the two normalized charts and lift it into the site.
  have hμp : (eX.hom ≫ σ ≫ eY.inv) ≫ (BigFppfOver.toScheme B S hS).map pY =
      (BigFppfOver.toScheme B S hS).map pX ≫ (BigFppfOver.toScheme B S hS).map φ := by
    rw [hpY, hpX, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hσ, Category.assoc]
  have hμcomp : (eX.hom ≫ σ ≫ eY.inv) ≫ B.inclusion.map Yν.hom
      = B.inclusion.map Xν.hom := by
    rw [← toScheme_map_comp_inclusion_hom B S hS pY,
      ← toScheme_map_comp_inclusion_hom B S hS pX,
      ← toScheme_map_comp_inclusion_hom B S hS φ, ← Category.assoc, hμp, Category.assoc]
  obtain ⟨m, hm⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS _ hμcomp
  have hmp : m ≫ pY = pX ≫ φ := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, Functor.map_comp, hm, hμp])
  refine ⟨inv gX ≫ yoneda.map m ≫ gY, ?_, ?_⟩
  · simp only [Category.assoc, hwY]
    rw [← Functor.map_comp, hmp, Functor.map_comp, ← hwX]
    simp
  · intro h' hh'
    have hh : h' ≫ DY.hom = DX.hom ≫ yoneda.map φ := hh'
    obtain ⟨m', hm'⟩ : ∃ m' : Xν ⟶ Yν, yoneda.map m' = gX ≫ h' ≫ inv gY :=
      ⟨yoneda.preimage _, yoneda.map_preimage _⟩
    have hm'p : m' ≫ pY = pX ≫ φ := by
      refine Yoneda.fullyFaithful.map_injective (C := BigFppfOver B S hS) ?_
      rw [Functor.map_comp, Functor.map_comp, hm', ← hwX, ← hwY]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [hh]
    have hσ' : (eX.inv ≫ (BigFppfOver.toScheme B S hS).map m' ≫ eY.hom) ≫
        ((BigFppfOver.toScheme B S hS).obj Y).normalization hY =
          ((BigFppfOver.toScheme B S hS).obj X).normalization hX ≫
            (BigFppfOver.toScheme B S hS).map φ := by
      simp only [Category.assoc]
      rw [← hpY, ← Functor.map_comp, hm'p, Functor.map_comp, hpX]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hmm : m' = m := (BigFppfOver.toScheme B S hS).map_injective (by
      rw [hm, ← hσu _ hσ']
      simp)
    rw [← hmm, hm']
    simp

end NormalizationData

end AlgebraicGeometry.Space

end
