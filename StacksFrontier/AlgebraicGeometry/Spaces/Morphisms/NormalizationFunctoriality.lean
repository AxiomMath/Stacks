module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.SmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of the normalization of an algebraic space

Let `F` and `G` be algebraic spaces over a scheme `S` of a big fppf site, with normalizations
`ν : F^ν ⟶ F` and `μ : G^ν ⟶ G` in the sense of `AlgebraicGeometry.Space.NormalizationData`.
The normalization is functorial, which is Tag 07U4: a morphism `f : F ⟶ G` carrying
codimension-zero points to codimension-zero points lifts uniquely to the normalizations — part
(3) — and for a smooth, in particular an étale, `f` those hypotheses hold and the lift
identifies the normalization of `F` with the fibre product `F ×_G G^ν` — part (4).

## Main statements

* `AlgebraicGeometry.Space.NormalizationData.existsUnique_normalizationLift`: **Tag 07U4,
  part (3)**.
* `AlgebraicGeometry.Space.NormalizationData.isIso_pullbackLift_of_isSmooth`: **Tag 07U4,
  part (4)**, for a smooth morphism.

## Implementation notes

Both statements are for arbitrary normalization data of the two spaces, which is the stronger
form. Part (3) is the universal property of the normalization of `G`, part (4) of Tag 0BB4
(`AlgebraicGeometry.Space.NormalizationData.existsUnique_lift_hom`), applied to the composite
`F^ν ⟶ F ⟶ G`. For part (4), `F ×_G G^ν` is terminal among normal algebraic spaces over `F`
preserving codimension zero in the same way `F^ν` is, which is read off one surjective étale
scheme chart of `F` over which the base change of `μ` is the normalization of the chart, by
Tag 07TD for a smooth morphism of schemes.

## References

* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace NormalizationData

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 07U4, part (3).** Let `f : F ⟶ G` be a morphism of algebraic spaces over `S`
carrying every point of codimension zero to a point of codimension zero, and let `ν : F^ν ⟶ F`
and `μ : G^ν ⟶ G` be normalizations. Then there is a unique morphism `f^ν : F^ν ⟶ G^ν` with
`μ ∘ f^ν = f ∘ ν`.

This is the universal property of the normalization of `G`, part (4) of Stacks 0BB4, applied to
the composite `F^ν ⟶ F ⟶ G`. Its two hypotheses on that composite are normality of `F^ν`, which
is part (1) of Stacks 0BB4, and preservation of codimension-zero points, which holds for `ν` by
part (3) of Stacks 0BB4 and for `f` by assumption. -/
@[stacks 07U4 "part (3), for arbitrary normalization data of the two spaces: the unique lift of a \
morphism preserving codimension-zero points"]
theorem existsUnique_normalizationLift {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : NormalizationData B S hS F) (D' : NormalizationData B S hS G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hgeneric : ∀ x : points B S hS F, localRingDimension B S hS x = 0 →
      localRingDimension B S hS (pointsMap B S hS F f x) = 0) :
    ∃! g : D.space ⟶ D'.space, g ≫ D'.hom = D.hom ≫ f :=
  D'.existsUnique_lift_hom hG D.isAlgebraicSpace (D.hasEtaleLocalProperty_isNormal hF)
    (D.hom ≫ f) fun z hz => by
      rw [pointsMap_comp_apply]
      exact hgeneric _ ((D.bijOn_codimensionZeroPoints_hom hF).mapsTo hz)

/-! ### Normalization and smooth base change -/

/-- **One chart of `F` over which the base change of the normalization morphism of `G` is the
normalization of the chart.** Let `f : F ⟶ G` be a smooth morphism of algebraic spaces over `S`
and let `μ : G^ν ⟶ G` be a normalization of `G`. Choose a surjective étale scheme atlas `V` of
`G`; over it `μ` base changes to the normalization of `V` by the chart condition. A surjective
étale scheme atlas `W` of `F` through which `f` lifts to a morphism `α : W ⟶ V` of the site
exists by Stacks 03I4, and `α` is smooth. Then
`F ×_G G^ν ×_F W = G^ν ×_G W = (G^ν ×_G V) ×_V W = V^ν ×_V W`, which is the normalization of `W`
by Stacks 07TD for the smooth `α`.

So the base change of `pullback.snd μ f : F ×_G G^ν ⟶ F` along the chart `W` is the
normalization of `W`: the chart condition of `AlgebraicGeometry.Space.NormalizationData` for
that morphism, at this one chart of `F`. -/
private theorem exists_chart_pullback_snd_of_isSmooth
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (D' : NormalizationData B S hS G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {f : F ⟶ G} (hf : IsSmooth B S hS f) :
    ∃ (W : BigFppfOver B S hS) (b : yoneda.obj W ⟶ F)
      (hW : ∀ V : ((BigFppfOver.toScheme B S hS).obj W).Opens,
        IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj W)) →
          (irreducibleComponents V).Finite)
      (Wν : BigFppfOver B S hS) (pW : Wν ⟶ W)
      (gW : yoneda.obj Wν ⟶ pullback D'.hom f)
      (e : ((BigFppfOver.toScheme B S hS).obj Wν) ≅
        Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj W) hW),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) b ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) b ∧
      (BigFppfOver.toScheme B S hS).map pW =
        e.hom ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj W) hW ∧
      IsPullback gW (yoneda.map pW) (pullback.snd D'.hom f) b := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨V, aG, haGs, haGe⟩ := hG.exists_atlas
  obtain ⟨hVfin, Vν, pV, gV, eV, hpV, hpbV⟩ := D'.chart V aG
    (isSurjective_of_presheafSurjective B S hS aG haGs)
    (isEtale_of_presheaf_etale B S hS haGe)
  obtain ⟨W, b, α, hcomm, hbs, hbe⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V aG haGs haGe
  have hαsm : AlgebraicGeometry.Smooth (T.map α) := hf W V b aG α hbe haGe hcomm.symm
  have hWfin := finite_irreducibleComponents_of_smooth (T.map α) hVfin
  -- the fibre product of the normalized chart with the chart, formed in the site
  have hsite : IsPullback (pullback.fst pV α) (pullback.snd pV α) pV α :=
    IsPullback.of_hasPullback _ _
  have hschemes : IsPullback
      ((BigFppfOver.toScheme B S hS).map (pullback.fst pV α) ≫ eV.hom)
      ((BigFppfOver.toScheme B S hS).map (pullback.snd pV α))
      (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj V) hVfin)
      ((BigFppfOver.toScheme B S hS).map α) := by
    have h := hsite.map (BigFppfOver.toScheme B S hS)
    rw [hpV] at h
    exact h.of_iso (Iso.refl _) eV (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
  -- normalization commutes with the smooth base change `α`
  have hnorm := isPullback_normalizationSchemeMap_of_smooth (T.map α) hVfin
  have houter : IsPullback (yoneda.map (pullback.fst pV α) ≫ gV)
      (yoneda.map (pullback.snd pV α)) D'.hom (b ≫ f) := by
    rw [hcomm]
    exact (hsite.map yoneda).paste_horiz hpbV
  refine ⟨W, b, hWfin, pullback pV α, pullback.snd pV α,
    (IsPullback.of_hasPullback D'.hom f).lift
      (yoneda.map (pullback.fst pV α) ≫ gV) (yoneda.map (pullback.snd pV α) ≫ b)
      (by rw [houter.w, Category.assoc]),
    hschemes.isoIsPullback _ _ hnorm, hbs, hbe,
    (hschemes.isoIsPullback_hom_snd _ _ hnorm).symm,
    houter.of_right' (IsPullback.of_hasPullback D'.hom f)⟩
/-- **Stacks 07U4, part (4).** Let `f : F ⟶ G` be a smooth — in particular an étale — morphism
of algebraic spaces over `S` with `G` satisfying the equivalent conditions of Stacks 0BB1, and
let `ν : F^ν ⟶ F` and `μ : G^ν ⟶ G` be normalizations. Then `F` satisfies the equivalent
conditions of Stacks 0BB1 and `f` carries points of codimension zero to points of codimension
zero — these are the hypotheses of part (3) — and the morphism `f^ν` of part (3) induces an
isomorphism `F^ν ⟶ F ×_G G^ν`.

The two hypotheses of part (3) are Stacks 0GMD and Stacks 0GMC for the flat, locally
finite-type morphism `f`.

For the isomorphism, `F ×_G G^ν` is terminal among normal algebraic spaces over `F` preserving
codimension zero in the same way `F^ν` is, and the comparison morphisms are therefore mutually
inverse. That `F ×_G G^ν` is such an object is read off one chart:
`AlgebraicGeometry.Space.NormalizationData.exists_chart_pullback_snd_of_isSmooth` exhibits a
surjective étale scheme chart of `F` over which `pullback.snd μ f` is the normalization of the
chart, which makes `F ×_G G^ν` normal — the chart of it so produced has a normal scheme — and
makes `pullback.snd μ f` preserve codimension zero, codimension zero being tested on that
chart. The universal property of `F^ν`, part (4) of Stacks 0BB4, then supplies the morphism
`F ×_G G^ν ⟶ F^ν` over `F`; its two composites with the canonical `F^ν ⟶ F ×_G G^ν` are
identities by the uniqueness halves of that property for `F` and for `G`. -/
@[stacks 07U4 "part (4), for a smooth morphism and arbitrary normalization data of the two spaces",
  sga "3 X 8.9" "partial"]
theorem isIso_pullbackLift_of_isSmooth {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : NormalizationData B S hS F) (D' : NormalizationData B S hS G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {f : F ⟶ G} (hf : IsSmooth B S hS f)
    (hGfin : HasLocallyFiniteIrreducibleComponents B S hS G) :
    HasLocallyFiniteIrreducibleComponents B S hS F ∧
      (∀ x : points B S hS F, localRingDimension B S hS x = 0 →
        localRingDimension B S hS (pointsMap B S hS F f x) = 0) ∧
      ∀ (g : D.space ⟶ D'.space) (hg : g ≫ D'.hom = D.hom ≫ f),
        IsIso (pullback.lift g D.hom hg) := by
  have hMemGen : ∀ {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS G)
      (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ G) (_ : IsEtale B S hS a)
      (z : points B S hS (yoneda.obj U)),
      localRingDimension B S hS (pointsMap B S hS (yoneda.obj U) a z) = 0 →
        pointsToScheme B S hS U z ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) :=
    fun hG U a ha z hz =>
      (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hG _).mp hz U a _ ha
        (chartPoint_pointsToScheme B S hS U a z)
  have hDimZero : ∀ {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS G)
      (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ G) (_ : IsEtale B S hS a)
      (z : points B S hS (yoneda.obj U)),
      pointsToScheme B S hS U z ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) →
        localRingDimension B S hS (pointsMap B S hS (yoneda.obj U) a z) = 0 :=
    fun hG U a ha z hz =>
      (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hG _).mpr
        ⟨U, a, _, ha, chartPoint_pointsToScheme B S hS U a z, hz⟩
  have hBijNorm : ∀ (X : Scheme.{u})
      (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite),
      Set.BijOn (X.normalization hX) (genericPoints (X.normalizationScheme hX))
        (genericPoints X) := by
    intro X hX
    obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
    have hred : IsReduced X.nilradical.subscheme := by
      simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
        Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := X) ⊤
    have hsurj : Function.Surjective X.nilradical.subschemeι := fun x ↦
      Set.mem_range.mp (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
    refine (((Homeomorph.bijOn_genericPoints
        (X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
          hsurj)).comp
      (X.nilradical.subscheme.isBirational_normalization
        (X.finite_irreducibleComponents_reduction hX)).bijOn).comp
      (Homeomorph.bijOn_genericPoints (Scheme.Hom.homeomorph e.hom))).congr
      fun x _ => ?_
    rw [← he]
    rfl
  have hflat := isFlat_of_isSmooth B S hS f hf
  have hgen : ∀ x : points B S hS F, localRingDimension B S hS x = 0 →
      localRingDimension B S hS (pointsMap B S hS F f x) = 0 :=
    fun x hx => localRingDimension_eq_zero_of_isFlat B S hS hF hG f hflat x hx
  refine ⟨hasLocallyFiniteIrreducibleComponents_of_isFlat_of_isLocallyOfFiniteType B S hS hF hG
    f hflat (isLocallyOfFiniteType_of_isSmooth B S hS hf) hGfin, hgen, fun g hg => ?_⟩
  obtain ⟨W, b, hW, Wν, pW, gW, e, hbs, hbe, hpW, hgW⟩ :=
    exists_chart_pullback_snd_of_isSmooth D' hF hG hf
  have hP : IsAlgebraicSpace B S hS (pullback D'.hom f) :=
    isAlgebraicSpace_pullback B S hS D'.hom f D'.isAlgebraicSpace hF hG
  have hbc : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange],
      (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (BigFppfOver.toScheme B S hS))) b →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (BigFppfOver.toScheme B S hS))) gW := fun P _ hb =>
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))).of_isPullback hgW.flip hb
  have hgWs := hbc _ hbs
  have hgWe := hbc _ hbe
  have hPnormal : HasEtaleLocalProperty B S hS (pullback D'.hom f)
      (fun Y : Scheme.{u} => IsNormal Y) :=
    ⟨Wν, gW, hgWs, hgWe, @_root_.AlgebraicGeometry.isNormal_of_iso _ _ e
      (Scheme.isNormal_normalizationScheme _ hW)⟩
  -- the projection to `F` preserves codimension zero, read on the chart `W`
  have hsnd : ∀ z : points B S hS (pullback D'.hom f), localRingDimension B S hS z = 0 →
      localRingDimension B S hS
        (pointsMap B S hS (pullback D'.hom f) (pullback.snd D'.hom f) z) = 0 := by
    intro z hz
    obtain ⟨z', hz'⟩ := isSurjective_of_presheafSurjective B S hS gW hgWs z
    have hz'gen := hMemGen hP Wν gW
      (isEtale_of_presheaf_etale B S hS hgWe) z' (by rw [hz']; exact hz)
    have hbij : Set.BijOn ((BigFppfOver.toScheme B S hS).map pW)
        (genericPoints ((BigFppfOver.toScheme B S hS).obj Wν))
        (genericPoints ((BigFppfOver.toScheme B S hS).obj W)) := by
      refine ((hBijNorm _ hW).comp
        (Homeomorph.bijOn_genericPoints (Scheme.Hom.homeomorph e.hom))).congr fun x _ => ?_
      rw [hpW]
      rfl
    have hWgen : pointsToScheme B S hS W
        (pointsMap B S hS (yoneda.obj Wν) (yoneda.map pW) z') ∈
          genericPoints ((BigFppfOver.toScheme B S hS).obj W) := by
      rw [pointsToScheme_pointsMap B S hS pW z']
      exact hbij.1 hz'gen
    have hchart := hDimZero hF W b
      (isEtale_of_presheaf_etale B S hS hbe) _ hWgen
    rw [← hz', ← pointsMap_comp_apply, hgW.w, pointsMap_comp_apply]
    exact hchart
  obtain ⟨a, ha, -⟩ := D.existsUnique_lift_hom hF hP hPnormal (pullback.snd D'.hom f) hsnd
  have h₁ : pullback.lift g D.hom hg ≫ a = 𝟙 D.space := by
    refine ExistsUnique.unique (D.existsUnique_lift_hom hF D.isAlgebraicSpace
      (D.hasEtaleLocalProperty_isNormal hF) D.hom
      fun z hz => (D.bijOn_codimensionZeroPoints_hom hF).mapsTo hz) ?_
      (Category.id_comp D.hom)
    rw [Category.assoc, ha, pullback.lift_snd]
  have hPG : ∀ z : points B S hS (pullback D'.hom f), localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS (pullback D'.hom f)
        (pullback.snd D'.hom f ≫ f) z) = 0 := by
    intro z hz
    rw [pointsMap_comp_apply]
    exact hgen _ (hsnd z hz)
  have h₂ : a ≫ pullback.lift g D.hom hg = 𝟙 (pullback D'.hom f) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine ExistsUnique.unique (D'.existsUnique_lift_hom hG hP hPnormal
        (pullback.snd D'.hom f ≫ f) hPG) ?_ pullback.condition
      rw [Category.assoc, hg, ← Category.assoc, ha]
    · rw [Category.assoc, pullback.lift_snd, ha, Category.id_comp]
  exact ⟨a, h₁, h₂⟩

end NormalizationData

end AlgebraicGeometry.Space

end
