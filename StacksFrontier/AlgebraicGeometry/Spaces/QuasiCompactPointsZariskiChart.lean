module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactZariskiLocalTarget

/-!
# From finite affine charts to a quasi-compact monomorphic representative

Stacks 03JV lists six equivalent conditions on a point `x` of an algebraic space `F` over a
scheme `S`. This file proves its condition (3) implies its condition (4): a monomorphic
field-valued representative of `x` whose base change to every affine étale chart of `F` is
finite is itself a quasi-compact morphism.

Together with the converse — the theorem
`hasMonomorphicFieldRepresentativeWithFiniteCharts` in the namespace
`AlgebraicGeometry.Space.HasQuasiCompactMonomorphicFieldRepresentative` — this makes
conditions (3) and (4) of Stacks 03JV equivalent.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.hasQuasiCompactMonomorphicFieldRepresentative_of_finiteCharts` is
  Stacks 03JV, condition (3) implies condition (4).

## Implementation notes

The source argues that `∐ Spec(k) ×_F U i ⟶ ∐ U i` is quasi-compact for a family of affine
étale charts covering `F`, and concludes by Stacks 03KG. The chart used here is a single
object `V` of the site with `h_V ⟶ F` surjective étale, which Stacks 03FX provides for any
algebraic space, and the coproduct is replaced by the covering of `V` by its affine open
subschemes:

* every point of `V` lies in an affine open of `V`, which is again an object of the site by
  `AlgebraicGeometry.exists_restrict_bigFppfOver`, and whose morphism to `V` is an open
  immersion, hence étale, hence composes with the chart to an affine étale chart of `F`;
* condition (3) applies to each of those charts, so the fibre product
  `Spec(k) ×_F W i` is finite over `Spec(k)`; since `Spec(k)` is an affine object of the site,
  the definition of a finite morphism represents that fibre product by an *affine* object `A`
  of the site, the comparison being an isomorphism because the base change is taken along an
  identity;
* the projection to `h_{W i}` is therefore the Yoneda image of a morphism `A ⟶ W i` of affine
  schemes, which is quasi-compact, so the projection is quasi-compact by Stacks 03HD;
* `AlgebraicGeometry.Space.isQuasiCompact_pullback_snd_of_openCover`, the Zariski-local
  criterion of Stacks 03KG (6), assembles the finitely many — indeed arbitrarily many —
  members into quasi-compactness of `Spec(k) ×_F V ⟶ h_V`, which is condition (4) of
  Stacks 03KG for the chart `h_V ⟶ F`;
* Stacks 03KG, condition (4) implies condition (1),
  `AlgebraicGeometry.Space.isQuasiCompact_of_surjectiveEtale_atlas`, concludes.

The covering of `V` is indexed by the points of the scheme underlying `V`, with a chosen
affine open neighbourhood at each point, so no finiteness or quasi-compactness of `V` is
needed; the Zariski-local criterion places no cardinality condition on the covering.

The monomorphism clause of condition (3) is carried through unchanged — it is not used, the
quasi-compactness of the representative being established from the finiteness clause alone —
and algebraicity of `F` is the standing hypothesis of the tag, used to produce the chart.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Every point of an object of the big fppf site over `S` lies in the image of an open
immersion from an object of the site with affine underlying scheme.

The affine opens of a scheme are a basis of its topology, and an open subscheme of an object
of the site is again an object of the site by
`AlgebraicGeometry.exists_restrict_bigFppfOver`; affineness is transported along the
isomorphism onto the open range. -/
private theorem exists_affine_open_bigFppfOver (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    ∃ (A : BigFppfOver B S hS) (jj : A ⟶ V),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jj) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      v ∈ Set.range ((BigFppfOver.toScheme B S hS).map jj) := by
  obtain ⟨O, hOaff, hvO, -⟩ := Opens.isBasis_iff_nbhd.1
    ((BigFppfOver.toScheme B S hS).obj V).isBasis_affineOpens
    (show v ∈ (⊤ : Opens ((BigFppfOver.toScheme B S hS).obj V)) from trivial)
  obtain ⟨A, jj, hjoi, hjrange, -⟩ := exists_restrict_bigFppfOver V O
  have hor : ((BigFppfOver.toScheme B S hS).map jj).opensRange = O := Opens.ext hjrange
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).map jj).opensRange := by
    rw [hor]; exact hOaff
  exact ⟨A, jj, hjoi,
    IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).map jj).isoOpensRange.hom,
    by rw [hjrange]; exact hvO⟩

/-- **Stacks 03JV, condition (3) implies condition (4).** Let `F` be an algebraic space over
`S` and let `x` be a point of `F`. If some field-valued representative of `x` presents it by
a monomorphism whose base change along every affine étale chart of `F` is finite, then that
monomorphism is in addition quasi-compact.

A surjective étale chart `h_V ⟶ F` by a single object of the site exists by Stacks 03FX, and
`V` is covered by its affine open subschemes, each of which is an object of the site whose
composite to `F` is an affine étale chart. The hypothesis applies to those charts, and the
resulting fibre products are affine objects of the site whose projections to the members of
the covering are morphisms of affine schemes, hence quasi-compact. The Zariski-local criterion
`AlgebraicGeometry.Space.isQuasiCompact_pullback_snd_of_openCover` turns that into
quasi-compactness of the base change of the representative along the chart, which is condition
(4) of Stacks 03KG, and
`AlgebraicGeometry.Space.isQuasiCompact_of_surjectiveEtale_atlas` is its condition (4) implies
condition (1).

Together with the converse this closes the adjacent equivalence of conditions (3) and
(4) of Stacks 03JV. -/
@[stacks 03JV "part (3) implies part (4)"]
theorem hasQuasiCompactMonomorphicFieldRepresentative_of_finiteCharts
    (hF : IsAlgebraicSpace B S hS F) {x : points B S hS F}
    (h : HasMonomorphicFieldRepresentativeWithFiniteCharts B S hS F x) :
    HasQuasiCompactMonomorphicFieldRepresentative B S hS F x := by
  classical
  obtain ⟨p, hpx, hmono, hfin⟩ := h
  refine ⟨p, hpx, hmono, ?_⟩
  obtain ⟨V, φ, hφS, hφE⟩ := hF.exists_atlas
  have hmulE := isMultiplicative_presheaf_etale B S hS
  choose W j hj hWaff hWcov using exists_affine_open_bigFppfOver B S hS V
  have hpaff : IsAffine ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))
  refine isQuasiCompact_of_surjectiveEtale_atlas B S hS (fieldMorphism B S hS F p)
    (isAlgebraicSpace_yoneda B S hS p.siteObject) hF V φ
    ((presheafSurjective_iff_isSurjective_yoneda B S hS F hF V φ).mp hφS)
    (isEtale_of_presheaf_etale B S hS hφE) ?_
  refine isQuasiCompact_pullback_snd_of_openCover B S hS (fieldMorphism B S hS F p)
    (isAlgebraicSpace_yoneda B S hS p.siteObject) hF V φ W j hj
    (fun v => ⟨v, hWcov v⟩) fun i => ?_
  -- The composite of an affine open of `V` with the chart is an affine étale chart of `F`.
  have hjE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (j i)) :=
    presheaf_yoneda_map_of_inverseImage B S hS inferInstance (j i)
      (have _ := hj i; inferInstance)
  have hψE : IsEtale B S hS (yoneda.map (j i) ≫ φ) :=
    isEtale_of_presheaf_etale B S hS
      (MorphismProperty.comp_mem _ (yoneda.map (j i)) φ hjE hφE)
  -- The fibre product over that chart is represented by an affine object of the site.
  obtain ⟨A, pr, ii, hAaff, hprfin, hsq⟩ :=
    hfin (W i) (hWaff i) (yoneda.map (j i) ≫ φ) hψE p.siteObject hpaff (𝟙 _)
  have _ : IsIso ii := hsq.isIso_fst_of_isIso
  obtain ⟨s, hs⟩ : ∃ s : A ⟶ W i, yoneda.map s =
      ii ≫ pullback.snd (fieldMorphism B S hS F p) (yoneda.map (j i) ≫ φ) :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hAaff
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (W i)) := hWaff i
  -- A morphism of affine schemes is quasi-compact, so Stacks 03HD applies.
  have hps : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map s) :=
    presheaf_yoneda_map_of_inverseImage B S hS inferInstance s inferInstance
  have heq : inv ii ≫ yoneda.map s =
      pullback.snd (fieldMorphism B S hS F p) (yoneda.map (j i) ≫ φ) := by
    rw [hs, IsIso.inv_hom_id_assoc]
  refine isQuasiCompact_of_presheaf_quasiCompact B S hS ?_
  rw [← heq]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hps

end AlgebraicGeometry.Space

end
