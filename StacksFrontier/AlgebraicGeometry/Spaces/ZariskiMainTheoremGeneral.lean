module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Zariski's main theorem for a quasi-finite separated morphism of algebraic spaces

Let `f : X ⟶ Y` be a quasi-finite separated morphism of algebraic spaces over a scheme `S`,
with **no representability hypothesis on either side**. Tag 0ABS asserts that the normalization
`X ⟶ Y' ⟶ Y` of `Y` in `X` exists, that the canonical morphism `X ⟶ Y'` is a quasi-compact open
immersion, that the normalization morphism `Y' ⟶ Y` is integral, and that `f` is quasi-affine.
This file proves the whole of that.

The normalization datum is glued along a surjective étale chart `w : h_U ⟶ Y` of the target:
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasRelation` makes the chart
normalizations `N(U ×_Y U) ⇉ N(U)` an étale equivalence relation,
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasQuotient` forms the quotient and the
two legs of the factorization and identifies `N(U)` with the fibre product of the quotient with
`U`, and `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasChart` descends that
identification to every étale chart of `Y`. The three assertions are then the theorems of
`StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremQuasiFinite`, read at that datum.

## Main results

* `AlgebraicGeometry.Space.NormalizationGluing.nonempty_normalizationInData`: a quasi-finite
  separated morphism of algebraic spaces over `S` has normalization data, with no
  representability and no size hypothesis.
* `AlgebraicGeometry.Space.zariskiMainTheorem`: **the whole of Tag 0ABS**, under exactly its own
  hypotheses — quasi-affineness of `f`, the existence of the normalization datum, the
  factorization of `f` through it, the open immersion, its quasi-compactness, and integrality
  of the normalization morphism, all in one statement.

## Implementation notes

**The chart condition is stated for an arbitrary representation of the fibre product.** The
chart condition of `AlgebraicGeometry.Space.NormalizationInData` quantifies over every object
`XW` of the site representing `W ×_Y X` and every cartesian square exhibiting it, not only over
the representation `AlgebraicGeometry.Space.NormalizationGluing` works with — the one chosen by
relative representability of `f`. The two differ by a unique isomorphism of charts over `W`
compatible with the projections to `X`, and the transition morphism of Tag 035J attached to it
is an isomorphism of chart normalizations by
`AlgebraicGeometry.Space.chartNormMap_comp_eq_id`, along which the chart datum transports.

**Why no size hypothesis.** The chart normalizations are objects of the site outright, by the
size bound `AlgebraicGeometry.Scheme.Hom.size_normalization_le`, and the quotient of an étale
equivalence relation of objects of the site is an algebraic space by Tag 02WW with no cardinal
condition.

## References

* [Stacks Project, Tag 0ABS](https://stacks.math.columbia.edu/tag/0ABS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 035J](https://stacks.math.columbia.edu/tag/035J)
* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.NormalizationGluing

/-- The chart of a quasi-compact relatively representable morphism over an object of the site
is quasi-compact. -/
theorem quasiCompact_hrep_snd_of_isQuasiCompact (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable f) (hqc : IsQuasiCompact B S hS f)
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y) :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd v)) :=
  ((presheaf_quasiCompact_iff_isQuasiCompact B S hS hrep).2 hqc).property v (hrep.fst v)
    (hrep.snd v) (hrep.isPullback v)

/-- The chart of a quasi-separated relatively representable morphism of algebraic spaces over
an object of the site is quasi-separated. -/
theorem quasiSeparated_hrep_snd_of_isQuasiSeparated (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable f) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hqs : IsQuasiSeparated B S hS f)
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y) :
    QuasiSeparated ((BigFppfOver.toScheme B S hS).map (hrep.snd v)) :=
  ((isQuasiSeparated_iff_presheaf B S hS f hX hY hrep).1 hqs).property v (hrep.fst v)
    (hrep.snd v) (hrep.isPullback v)

/-- **A quasi-compact quasi-separated representable morphism of algebraic spaces has
normalization data** (the normalization of Tag 0BAK, as the chart datum of Tag 0ABP). The datum
is glued from the chart normalizations along a surjective étale chart of the target; no
representability of either side and no bound on sizes is assumed. -/
theorem nonempty_normalizationInData_of_isQuasiCompact_isQuasiSeparated (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hqc : IsQuasiCompact B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    Nonempty (NormalizationInData B S hS f) := by
  obtain ⟨U, w, hwsurj, hwet⟩ := hY.exists_atlas
  obtain ⟨R, pr₁, pr₂, hsq⟩ := exists_kernelPair_of_etale_atlas B S hS w hwet
  have _ {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y) :=
    quasiCompact_hrep_snd_of_isQuasiCompact B S hS hrep hqc v
  have _ {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y) :=
    quasiSeparated_hrep_snd_of_isQuasiSeparated B S hS hrep hX hY hqs v
  refine ⟨{ space := normQuot B S hS hrep w pr₁ pr₂ hsq
            isAlgebraicSpace := isAlgebraicSpace_normQuot B S hS hrep w pr₁ pr₂ hsq hwet
            toNorm := toNormQuot B S hS hrep w pr₁ pr₂ hsq hwet hX hwsurj
            fromNorm := normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY
            fac := toNormQuot_comp_normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hX hY hwsurj
            chart := ?_ }⟩
  intro W XW w' p a hw'et hsq' _ _
  have hw' : yoneda.relativelyRepresentable w' :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS hY w'
  obtain ⟨bW, hbWpb, hbWunit⟩ := exists_chartMapToSpace B S hS hrep w pr₁ pr₂ hsq
    (isAlgebraicSpace_normQuot B S hS hrep w pr₁ pr₂ hsq hwet)
    (normQuotToBase B S hS hrep w pr₁ pr₂ hsq hwet hY)
    (toNormQuot B S hS hrep w pr₁ pr₂ hsq hwet hX hwsurj)
    (normQuotMap B S hS hrep w pr₁ pr₂ hsq)
    (isPullback_normQuotMap_self B S hS hrep w pr₁ pr₂ hsq hwet)
    (isPullback_normQuotMap B S hS hrep w pr₁ pr₂ hsq hwet hY)
    (chartFst_comp_toNormQuot B S hS hrep w pr₁ pr₂ hsq hwet hX hwsurj).symm
    hwsurj hwet hY w' hw'et (hw'.fst' w) (hw'.snd w) (hw'.isPullback' w)
  -- the given representation of the fibre product and the chosen one are isomorphic over `W`
  have hιfst : yoneda.map (hrep.lift a p hsq'.w) ≫ hrep.fst w' = a := hrep.lift_fst _ _ _
  have hιsnd : hrep.lift a p hsq'.w ≫ hrep.snd w' = p := hrep.lift_snd _ _ _
  obtain ⟨ι', hι'⟩ : ∃ ι' : hrep.pullback w' ⟶ XW, yoneda.map ι' =
      hsq'.lift (hrep.fst w') (yoneda.map (hrep.snd w')) (hrep.isPullback w').w :=
    ⟨_, yoneda.map_preimage _⟩
  have hι'a : yoneda.map ι' ≫ a = hrep.fst w' := by
    rw [hι']
    exact hsq'.lift_fst _ _ _
  have hι'p : ι' ≫ p = hrep.snd w' :=
    yoneda.map_injective (by rw [Functor.map_comp, hι']; exact hsq'.lift_snd _ _ _)
  have hιι' : hrep.lift a p hsq'.w ≫ ι' = 𝟙 XW := by
    refine yoneda.map_injective (hsq'.hom_ext ?_ ?_)
    · rw [Functor.map_comp, Category.assoc, hι'a, hιfst, CategoryTheory.Functor.map_id,
        Category.id_comp]
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hι'p, hιsnd, Category.id_comp]
  have hι'ι : ι' ≫ hrep.lift a p hsq'.w = 𝟙 (hrep.pullback w') := by
    refine hrep.hom_ext ?_ ?_
    · rw [Functor.map_comp, Category.assoc, hιfst, hι'a, CategoryTheory.Functor.map_id,
        Category.id_comp]
    · rw [Category.assoc, hιsnd, hι'p, Category.id_comp]
  have hsqι : hrep.lift a p hsq'.w ≫ hrep.snd w' = p ≫ 𝟙 W := by
    rw [hιsnd, Category.comp_id]
  have hsqι' : ι' ≫ p = hrep.snd w' ≫ 𝟙 W := hι'p.trans (Category.comp_id _).symm
  have _ : IsIso (chartNormMap B S hS (hrep.snd w') p (𝟙 W) (hrep.lift a p hsq'.w) hsqι) :=
    ⟨_, chartNormMap_comp_eq_id B S hS p (hrep.snd w') (𝟙 W) ι' hsqι' (𝟙 W)
      (hrep.lift a p hsq'.w) hsqι (by simp) hιι',
    chartNormMap_comp_eq_id B S hS (hrep.snd w') p (𝟙 W) (hrep.lift a p hsq'.w) hsqι (𝟙 W) ι'
      hsqι' (by simp) hι'ι⟩
  have hcmproj : chartNormMap B S hS (hrep.snd w') p (𝟙 W) (hrep.lift a p hsq'.w) hsqι ≫
      chartNormProj B S hS (hrep.snd w') = chartNormProj B S hS p := by
    rw [chartNormMap_comp_chartNormProj, Category.comp_id]
  refine exists_chart_of_isPullback B S hS _ _ w' p a
    (yoneda.map (chartNormMap B S hS (hrep.snd w') p (𝟙 W) (hrep.lift a p hsq'.w) hsqι) ≫ bW)
    ?_ ?_
  · refine IsPullback.of_iso_pullback ⟨?_⟩
      (asIso (yoneda.map (chartNormMap B S hS (hrep.snd w') p (𝟙 W)
        (hrep.lift a p hsq'.w) hsqι)) ≪≫ hbWpb.isoPullback) ?_ ?_
    · rw [Category.assoc, hbWpb.w, ← Functor.map_comp_assoc, hcmproj]
    · rw [Iso.trans_hom, asIso_hom, Category.assoc, hbWpb.isoPullback_hom_fst]
    · rw [Iso.trans_hom, asIso_hom, Category.assoc, hbWpb.isoPullback_hom_snd,
        ← Functor.map_comp, hcmproj]
  · rw [← Functor.map_comp_assoc, chartNormUnit_comp_chartNormMap, Functor.map_comp_assoc,
      hbWunit, ← Category.assoc, hιfst]

/-- **A quasi-finite separated morphism of algebraic spaces has normalization data.** The datum
is glued from the chart normalizations along a surjective étale chart of the target; no
representability of either side and no bound on sizes is assumed. -/
theorem nonempty_normalizationInData (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f) :
    Nonempty (NormalizationInData B S hS f) :=
  nonempty_normalizationInData_of_isQuasiCompact_isQuasiSeparated B S hS f hX hY
    (relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f hX hY hqf.1 hsep)
    hqf.2 (isQuasiSeparated_of_isSeparated B S hS hsep)

end AlgebraicGeometry.Space.NormalizationGluing

namespace AlgebraicGeometry.Space

/-- **Zariski's main theorem for algebraic spaces.** Let `f : X ⟶ Y` be a quasi-finite
separated morphism of algebraic spaces over a scheme `S`. Then `f` is quasi-affine, and the
normalization of `Y` in `X` exists: there is a factorization `X --f'--> Y' --ν--> Y` of `f`
whose base change along every étale scheme chart of `Y` is the relative normalization of that
chart, in which `f'` is a quasi-compact open immersion and `ν` is integral.

Neither side is required to be representable and no bound on sizes is assumed: the datum is
glued along a surjective étale chart of the target in
`AlgebraicGeometry.Space.NormalizationGluing.nonempty_normalizationInData`, and the four
assertions about it are the theorems of
`StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremQuasiFinite`. -/
@[stacks 0ABS, ega "III 4.4.12" "more general"]
theorem zariskiMainTheorem (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqf : IsQuasiFinite B S hS f) (hsep : IsSeparated B S hS f) :
    IsQuasiAffineHom B S hS f ∧
      ∃ N : NormalizationInData B S hS f,
        N.toNorm ≫ N.fromNorm = f ∧
        IsOpenImmersion B S hS N.toNorm ∧
        IsQuasiCompact B S hS N.toNorm ∧
        IsIntegralHom B S hS N.fromNorm := by
  obtain ⟨N⟩ := NormalizationGluing.nonempty_normalizationInData B S hS f hX hY hqf hsep
  exact ⟨isQuasiAffineHom_of_isQuasiFinite_isSeparated hX hY hqf hsep,
    N, N.fac,
    N.isOpenImmersion_toNorm_of_isQuasiFinite_isSeparated hX hY hqf hsep,
    N.isQuasiCompact_toNorm_of_isQuasiFinite_isSeparated hX hY hqf hsep,
    N.isIntegralHom_fromNorm_of_isQuasiFinite_isSeparated hX hY hqf hsep⟩

end AlgebraicGeometry.Space

end
