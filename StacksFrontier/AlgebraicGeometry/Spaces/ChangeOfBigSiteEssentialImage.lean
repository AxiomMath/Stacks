module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismsOfTopoi

/-!
# The functor on algebraic spaces given by enlarging the big fppf site

Enlarging a big fppf site gives, by Stacks 03FP, a functor from the algebraic spaces over `S`
defined using the smaller site to those defined using the larger one. That functor is fully
faithful, because the inverse image along a fully faithful cocontinuous functor of sites is;
and an algebraic space `X'` over the larger site lies in its essential image exactly when there
are objects `U` and `R` of the *smaller* site together with maps `U ⟶ X'` and
`R ⟶ U ×_{X'} U` which are surjective as maps of sheaves.

## Main definitions

* `AlgebraicGeometry.changeBigSiteOfDescent` is inverse image along the inclusion of localized
  big fppf sites, as a functor on algebraic spaces.

## Main results

* `AlgebraicGeometry.changeBigSiteOfDescent_fullyFaithful` — full faithfulness.
* `AlgebraicGeometry.exists_small_presentation_of_mem_essentialImage` and
  `AlgebraicGeometry.mem_essentialImage_of_small_presentation` — the two halves of the
  characterization of the essential image, combined in
  `AlgebraicGeometry.mem_essentialImage_changeBigSiteOfDescent_iff`.

## Implementation notes

Surjectivity of a map of sheaves is expressed by `CategoryTheory.Presheaf.IsLocallySurjective`
for the fppf topology of the larger localized site. The second presentation map is not
redundant: the fibre product `U ×_{X'} U` can be larger than any bound the smaller site's cutoff
allows, which is why the source's statement asks for `R` as well, and why the size bounds of
`StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds` are needed to produce `V` and `Q`
inside the smaller site.

Full faithfulness is Stacks 00XU for the localized inclusion, which is cocontinuous, continuous
and fully faithful, transported along the two fully faithful functors that present algebraic
spaces as a full subcategory of presheaves.

The quotient theorem Stacks 02WW is available in this library only relative to effective descent
along the covering sieves of the site at the monomorphisms locally of finite type, so every
statement below carries that hypothesis — for the larger site when only the functor is involved,
and for both sites in the essential-image characterization. The statement of Stacks 04W1 itself
has no such hypothesis.

## References

* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Space Stacks.Groupoids

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- Effective descent along the covering sieves of a big fppf site at the monomorphisms locally
of finite type: the hypothesis of the quotient theorem Stacks 02WW in the form in which this
library has it. -/
abbrev DescentForQuotients (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  Space.IsEffectiveDescentAlongCoveringSieve B S hS
    (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)

/-- **Stacks 03FP and 04W1, the functor**, relative to effective descent along the covering
sieves of the larger site at the monomorphisms locally of finite type.

Inverse image along the inclusion of localized big fppf sites, as a functor from the algebraic
spaces over `S` defined using `B` to those defined using `B'`. -/
def changeBigSiteOfDescent (hdesc : DescentForQuotients B' S (largerContains h hS)) :
    AlgebraicSpaces B S hS ⥤ AlgebraicSpaces B' S (largerContains h hS) := by
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  letI : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let toSheaf : AlgebraicSpaces B S hS ⥤ Sheaf J (Type u) :=
    ObjectProperty.lift _ (ObjectProperty.ι _) fun X => X.property.isSheaf
  exact ObjectProperty.lift
    (P := fun F => IsAlgebraicSpace B' S (largerContains h hS) F)
    (toSheaf ⋙ i.sheafPullback (Type u) J K ⋙ sheafToPresheaf K (Type u))
    fun X => isAlgebraicSpace_sheafPullback_of_descent B B' h S hS X.obj X.property hdesc

/-- **Stacks 04W1, full faithfulness**, relative to effective descent along the covering sieves
of the larger site at the monomorphisms locally of finite type.

Inverse image along the inclusion of localized big fppf sites is fully faithful on algebraic
spaces. -/
theorem changeBigSiteOfDescent_fullyFaithful
    (hdesc : DescentForQuotients B' S (largerContains h hS)) :
    Nonempty (changeBigSiteOfDescent B B' h S hS hdesc).FullyFaithful := by
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : i.IsCocontinuous J K := inclusionOver_isCocontinuous (τ := .fppf) B B' h S hS
  let : i.Full := inclusionOver_full h S hS
  let : i.Faithful := inclusionOver_faithful h S hS
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : EssentiallySmall.{u} (siteCategory (τ := .fppf) B) := essentiallySmall_schemeBelow _
  let : EssentiallySmall.{u} (siteCategory (τ := .fppf) B') := essentiallySmall_schemeBelow _
  let : EssentiallySmall.{u} (Over (base (τ := .fppf) B S hS)) :=
    essentiallySmall_bigFppfOver B S hS
  let : EssentiallySmall.{u} (Over (base (τ := .fppf) B' S (largerContains h hS))) :=
    essentiallySmall_bigFppfOver B' S (largerContains h hS)
  let : ∀ F : (Over (base (τ := .fppf) B S hS))ᵒᵖ ⥤ Type u,
      i.op.HasPointwiseRightKanExtension F := by
    intro F Y
    let : HasLimitsOfShape (StructuredArrow Y i.op) (Type u) :=
      hasLimitsOfShape_of_essentiallySmall.{u} _ _
    show HasLimit (StructuredArrow.proj Y i.op ⋙ F)
    infer_instance
  have hpullff := Functor.full_and_faithful_sheafPullback i (Type u) J K
  let : (i.sheafPullback (Type u) J K).Full := hpullff.1
  let : (i.sheafPullback (Type u) J K).Faithful := hpullff.2
  unfold changeBigSiteOfDescent
  let toSheaf : AlgebraicSpaces B S hS ⥤ Sheaf J (Type u) :=
    ObjectProperty.ιOfLE fun _ hX => hX.isSheaf
  let G : AlgebraicSpaces B S hS ⥤
      (BigFppfOver B' S (largerContains h hS))ᵒᵖ ⥤ Type u :=
    toSheaf ⋙ i.sheafPullback (Type u) J K ⋙ sheafToPresheaf K (Type u)
  have hto : toSheaf.FullyFaithful := ObjectProperty.fullyFaithfulιOfLE _
  have hpull : (i.sheafPullback (Type u) J K).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  have hG : G.FullyFaithful :=
    hto.comp (hpull.comp (fullyFaithfulSheafToPresheaf K (Type u)))
  let : G.Full := hG.full
  let : G.Faithful := hG.faithful
  let P' := fun F : (BigFppfOver B' S (largerContains h hS))ᵒᵖ ⥤ Type u =>
    IsAlgebraicSpace B' S (largerContains h hS) F
  let hP' := fun X : AlgebraicSpaces B S hS =>
    isAlgebraicSpace_sheafPullback_of_descent B B' h S hS X.obj X.property hdesc
  let L := ObjectProperty.lift P' G hP'
  let : L.Full := Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso P' G hP')
  let : L.Faithful := Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso P' G hP')
  exact ⟨Functor.FullyFaithful.ofFullyFaithful L⟩

/-- **Stacks 04W1, the small presentation.** An algebraic space over `S` on the larger site which
receives locally surjective maps from an object `U` of the smaller site and, on its kernel pair,
from an object `R` of the smaller site, has a surjective étale atlas and a kernel pair both of
which already come from the smaller site.

This is where the size bounds of
`StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds` are used. -/
theorem exists_small_atlas_and_relation
    {F : (BigFppfOver B' S (largerContains h hS))ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B' S (largerContains h hS) F) (U R : BigFppfOver B S hS)
    (f : yoneda.obj ((inclusionOver h S hS).obj U) ⟶ F)
    (g : yoneda.obj ((inclusionOver h S hS).obj R) ⟶ pullback f f)
    (hf : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B' S (largerContains h hS)) f)
    (hg : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B' S (largerContains h hS)) g) :
    let i := inclusionOver h S hS
    ∃ (V Q : BigFppfOver B S hS) (r s : Q ⟶ V) (q : yoneda.obj (i.obj V) ⟶ F),
      IsPullback (yoneda.map (i.map r)) (yoneda.map (i.map s)) q q ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B' S (largerContains h hS)))) q ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B' S (largerContains h hS)))) q := by
  let hS' : B'.Contains S := largerContains h hS
  let i := inclusionOver h S hS
  let J := BigFppfOver.topology B' S hS'
  let : HasBinaryProducts (BigFppfOver B' S hS') :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hfr := hF.diagonal_representable.of_diag f
  let D := hfr.pullback f
  let ds := hfr.fst' f
  let dt := hfr.snd f
  have hD : IsPullback (yoneda.map ds) (yoneda.map dt) f f := hfr.isPullback' f
  let eD := hD.isoPullback
  let g' : i.obj R ⟶ D := yoneda.preimage (g ≫ eD.symm.hom)
  have hg' : Presheaf.IsLocallySurjective J (yoneda.map g') :=
    Presheaf.isLocallySurjective_yoneda_map_preimage_comp_iso J g hg eD.symm
  have hDsize : D.left.obj.size < B.cutoff :=
    (size_le_of_isLocallySurjective B' S hS' g' hg').trans_lt R.left.property
  obtain ⟨V, q, hV, hqs, hqe⟩ := exists_atlas_size_le B' S hS' hF f hf
  let W := hfr.pullback q
  let wU : W ⟶ i.obj U := hfr.fst' q
  let wV : W ⟶ V := hfr.snd q
  have hW : IsPullback (yoneda.map wU) (yoneda.map wV) f q := hfr.isPullback' q
  have hwV : Presheaf.IsLocallySurjective J (yoneda.map wV) :=
    Presheaf.isLocallySurjective_of_isPullback J hW.flip (hf := hf)
  obtain ⟨T, t, w, hwt, hT, ht⟩ := exists_bounded_fppf_lift B' S hS' wV hwV
  let Q := hqe.rep.pullback q
  let r := hqe.rep.fst' q
  let s := hqe.rep.snd q
  have hQ : IsPullback (yoneda.map r) (yoneda.map s) q q := hqe.rep.isPullback' q
  have hfac : yoneda.map (w ≫ wU) ≫ f = yoneda.map t ≫ q :=
    yoneda_map_comp_fac hW.w hwt
  have hQsize : Q.left.obj.size < B.cutoff :=
    (size_kernelPair_le B' S hS' hD hQ (w ≫ wU) t hfac ht).trans_lt
      (max_lt hDsize (hT.trans_lt (hV.trans_lt U.left.property)))
  let V₀ : BigFppfOver B S hS :=
    Over.mk (Y := B.obj (hV.trans_lt U.left.property)) (X := B.obj hS) ⟨V.hom.hom⟩
  let Q₀ : BigFppfOver B S hS := Over.mk (Y := B.obj hQsize) (X := B.obj hS) ⟨Q.hom.hom⟩
  let res (a : Q ⟶ V) : Q₀ ⟶ V₀ := Over.homMk ⟨a.left.hom⟩ (by
    apply ObjectProperty.hom_ext
    show a.left.hom ≫ V.hom.hom = Q.hom.hom
    exact congrArg InducedCategory.Hom.hom (Over.w a))
  exact ⟨V₀, Q₀, res r, res s, q, hQ, hqs, hqe⟩

/-- A pair `s, t` which is an equivalence relation after `Over.post`, with both maps étale, is an
étale equivalence relation. -/
private theorem isEtaleEquivalenceRelation_relation_of_etale
    {R U : BigFppfOver B S hS} (s t : R ⟶ U)
    (hrel : IsEquivalenceRelation ((Over.post B.inclusion).map s) ((Over.post B.inclusion).map t))
    (hs : Etale ((Over.post B.inclusion).map s).left)
    (ht : Etale ((Over.post B.inclusion).map t).left) :
    IsEtaleEquivalenceRelation (relation B S hS t s) where
  isEquivalenceRelation := by
    simpa only [relation, PreRelation.target, PreRelation.source, prod.lift_fst, prod.lift_snd]
      using hrel
  etale_source := by simpa only [relation, PreRelation.source, prod.lift_snd] using ht
  etale_target := by simpa only [relation, PreRelation.target, prod.lift_fst] using hs

/-- If `s, t` is the kernel pair of a locally surjective map `q` from a representable presheaf,
then composing `q` with an isomorphism `e` gives a locally surjective map onto whose kernel pair
`R` maps locally surjectively. -/
private theorem exists_isLocallySurjective_of_isPullback_of_iso {C : Type*} [Category.{u} C]
    (K : GrothendieckTopology C) {U R : C} {Q X : Cᵒᵖ ⥤ Type u} (q : yoneda.obj U ⟶ Q)
    (s t : R ⟶ U) (hR : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (hq : Presheaf.IsLocallySurjective K q) (e : Q ≅ X) :
    ∃ g : yoneda.obj R ⟶ pullback (q ≫ e.hom) (q ≫ e.hom),
      Presheaf.IsLocallySurjective K (q ≫ e.hom) ∧ Presheaf.IsLocallySurjective K g := by
  have hRe : IsPullback (yoneda.map s) (yoneda.map t) (q ≫ e.hom) (q ≫ e.hom) :=
    hR.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
      (Category.id_comp _).symm (Category.id_comp _).symm
  have : Presheaf.IsLocallySurjective K e.hom := Presheaf.isLocallySurjective_of_iso K e.hom
  exact ⟨hRe.isoPullback.hom, Presheaf.isLocallySurjective_comp K q e.hom,
    Presheaf.isLocallySurjective_of_iso K _⟩

/-- Two surjective étale presentations with the same kernel pair, one on each site, show that the
inverse image of the first algebraic space is the second. -/
private theorem nonempty_iso_sheafPullback_of_isPullback
    [(inclusionOver h S hS).IsContinuous (overTopology .fppf B S hS)
      (overTopology .fppf B' S (largerContains h hS))]
    [((inclusionOver h S hS).sheafPushforwardContinuous (Type u) (overTopology .fppf B S hS)
      (overTopology .fppf B' S (largerContains h hS))).IsRightAdjoint]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : (BigFppfOver B' S (largerContains h hS))ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B' S (largerContains h hS) G)
    {U R : BigFppfOver B S hS} (s t : R ⟶ U) (q : yoneda.obj U ⟶ F)
    (q' : yoneda.obj ((inclusionOver h S hS).obj U) ⟶ G)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (hR' : IsPullback (yoneda.map ((inclusionOver h S hS).map s))
      (yoneda.map ((inclusionOver h S hS).map t)) q' q')
    (hqs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hqe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hqs' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS)))) q')
    (hqe' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS)))) q') :
    Nonempty (((inclusionOver h S hS).sheafPullback (Type u)
      (overTopology .fppf B S hS) (overTopology .fppf B' S (largerContains h hS))).obj
        ⟨F, hF.isSheaf⟩ ≅ ⟨G, hG.isSheaf⟩) ∧
      Presheaf.IsLocallySurjective (overTopology .fppf B' S (largerContains h hS)) q' := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S hS'
  let : J.Subcanonical := subcanonical_overTopology B S hS
  let : K.Subcanonical := subcanonical_overTopology B' S hS'
  obtain ⟨_, _, ⟨hq⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS q s t hR hF hqs hqe
  obtain ⟨_, _, ⟨hq'⟩⟩ := isCoequalizer_of_surjectiveEtale B' S hS' q' (i.map s) (i.map t) hR' hG
    hqs' hqe'
  let : PreservesColimits (i.sheafPullback (Type u) J K) :=
    (i.sheafAdjunctionContinuous (Type u) J K).leftAdjoint_preservesColimits
  let q'Sheaf : K.yoneda.obj (i.obj U) ⟶ (⟨G, hG.isSheaf⟩ : Sheaf K (Type u)) := ⟨q'⟩
  exact ⟨⟨coequalizerIsoOfNatIso J.yoneda (i ⋙ K.yoneda) (i.sheafPullback (Type u) J K)
    (pullbackYonedaIso i J K) s t
    (show J.yoneda.obj U ⟶ (⟨F, hF.isSheaf⟩ : Sheaf J (Type u)) from ⟨q⟩)
    (by apply Sheaf.hom_ext; exact hR.w) q'Sheaf
    (by apply Sheaf.hom_ext; exact hR'.w) hq hq'⟩,
    (Sheaf.isLocallySurjective_iff_epi q'Sheaf).mpr (Cofork.IsColimit.epi hq')⟩

/-- **Stacks 04W1, one half of the essential image**, relative to effective descent along the
covering sieves of the larger site.

An algebraic space over `S` in the essential image of inverse image along the inclusion of
localized big fppf sites receives locally surjective maps from an object of the smaller site and
from an object of the smaller site onto its kernel pair. -/
theorem exists_small_presentation_of_mem_essentialImage
    (hdesc : DescentForQuotients B' S (largerContains h hS))
    (X : AlgebraicSpaces B S hS) (X' : AlgebraicSpaces B' S (largerContains h hS))
    (eX : (changeBigSiteOfDescent B B' h S hS hdesc).obj X ≅ X') :
    let K := BigFppfOver.topology B' S (largerContains h hS)
    let i := inclusionOver h S hS
    ∃ (U R : BigFppfOver B S hS) (f : yoneda.obj (i.obj U) ⟶ X'.obj)
      (g : yoneda.obj (i.obj R) ⟶ pullback f f),
      Presheaf.IsLocallySurjective K f ∧ Presheaf.IsLocallySurjective K g := by
  let hS' : B'.Contains S := largerContains h hS
  have hF := X.property
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S hS'
  obtain ⟨U, q, hqs, hqe⟩ := hF.exists_atlas
  let R := hqe.rep.pullback q
  let s : R ⟶ U := hqe.rep.fst' q
  let t : R ⟶ U := hqe.rep.snd q
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := hqe.rep.isPullback' q
  let : IsEtaleEquivalenceRelation (relation B' S hS' (i.map t) (i.map s)) :=
    isEtaleEquivalenceRelation_relation_of_etale B S hS s t
      (isEquivalenceRelation_of_isPullback B S hS q s t hR)
      (hqe.property q (yoneda.map t) s hR.flip) (hqe.property q (yoneda.map s) t hR)
  let Q := quotientSheaf K (Over.post B'.inclusion) (relation B' S hS' (i.map t) (i.map s))
  have hQ : IsAlgebraicSpace B' S hS' Q.obj :=
    isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B' S hS' (i.map t) (i.map s) hdesc
  let q' : yoneda.obj (i.obj U) ⟶ Q.obj := quotientMap B' S hS' (i.map t) (i.map s)
  have hR' : IsPullback (yoneda.map (i.map s)) (yoneda.map (i.map t)) q' q' :=
    quotientMap_isPullback B' S hS' (i.map t) (i.map s)
  have hQrep : yoneda.relativelyRepresentable (quotientMap B' S hS' (i.map t) (i.map s)) :=
    relativelyRepresentable_quotientMap_of_isAlgebraicSpace B' S hS' (i.map t) (i.map s) hQ
  have hqe' := quotientMap_etale B' S hS' (i.map t) (i.map s) hQrep
  obtain ⟨⟨e⟩, hq'⟩ := nonempty_iso_sheafPullback_of_isPullback B B' h S hS hF hQ s t q q' hR hR'
    hqs hqe (quotientMap_surjective B' S hS' (i.map t) (i.map s) hQrep) hqe'
  exact ⟨U, R, _, exists_isLocallySurjective_of_isPullback_of_iso K q' (i.map s) (i.map t) hR'
    hq' (show Q.obj ≅ X'.obj from
      ((sheafToPresheaf K (Type u)).mapIso e).symm ≪≫ (ObjectProperty.ι _).mapIso eX)⟩

/-- **Stacks 04W1, the other half of the essential image**, relative to effective descent along
the covering sieves of both sites.

An algebraic space over `S` on the larger site which receives locally surjective maps from an
object of the smaller site and from an object of the smaller site onto its kernel pair lies in
the essential image of inverse image along the inclusion of localized big fppf sites. -/
theorem mem_essentialImage_of_small_presentation
    (hdesc : DescentForQuotients B S hS)
    (hdesc' : DescentForQuotients B' S (largerContains h hS))
    (X' : AlgebraicSpaces B' S (largerContains h hS)) (U R : BigFppfOver B S hS)
    (f : yoneda.obj ((inclusionOver h S hS).obj U) ⟶ X'.obj)
    (g : yoneda.obj ((inclusionOver h S hS).obj R) ⟶ pullback f f)
    (hf : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B' S (largerContains h hS)) f)
    (hg : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B' S (largerContains h hS)) g) :
    ∃ X : AlgebraicSpaces B S hS,
      Nonempty ((changeBigSiteOfDescent B B' h S hS hdesc').obj X ≅ X') := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S hS'
  obtain ⟨V, Q, r, s, q, hQ, hqs, hqe⟩ :=
    exists_small_atlas_and_relation B B' h S hS X'.property U R f g hf hg
  let : IsEtaleEquivalenceRelation (relation B S hS s r) :=
    isEtaleEquivalenceRelation_relation_of_etale B S hS r s
      (isEquivalenceRelation_of_isPullback B' S hS' q (i.map r) (i.map s) hQ)
      (hqe.property q (yoneda.map (i.map s)) (i.map r) hQ.flip)
      (hqe.property q (yoneda.map (i.map r)) (i.map s) hQ)
  let F := quotientSheaf J (Over.post B.inclusion) (relation B S hS s r)
  have hF : IsAlgebraicSpace B S hS F.obj :=
    isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s r hdesc
  have hFrep : yoneda.relativelyRepresentable (quotientMap B S hS s r) :=
    relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s r hF
  obtain ⟨⟨e⟩, -⟩ := nonempty_iso_sheafPullback_of_isPullback B B' h S hS hF X'.property r s
    (quotientMap B S hS s r) q (quotientMap_isPullback B S hS s r) hQ
    (quotientMap_surjective B S hS s r hFrep) (quotientMap_etale B S hS s r hFrep) hqs hqe
  exact ⟨⟨F.obj, hF⟩, ⟨ObjectProperty.isoMk _ ((sheafToPresheaf K (Type u)).mapIso e)⟩⟩

/-- **Stacks 04W1, the essential image**, relative to effective descent along the covering sieves
of both sites at the monomorphisms locally of finite type.

An algebraic space on the enlarged big fppf site descends precisely when a scheme of the smaller
site surjects onto it and another scheme of the smaller site surjects onto the kernel pair of
that surjection. -/
theorem mem_essentialImage_changeBigSiteOfDescent_iff
    (hdesc : DescentForQuotients B S hS)
    (hdesc' : DescentForQuotients B' S (largerContains h hS))
    (X' : AlgebraicSpaces B' S (largerContains h hS)) :
    (∃ X : AlgebraicSpaces B S hS,
      Nonempty ((changeBigSiteOfDescent B B' h S hS hdesc').obj X ≅ X')) ↔
      (letI K := BigFppfOver.topology B' S (largerContains h hS)
       let i := inclusionOver h S hS
       ∃ (U R : BigFppfOver B S hS) (f : yoneda.obj (i.obj U) ⟶ X'.obj)
         (g : yoneda.obj (i.obj R) ⟶ pullback f f),
         Presheaf.IsLocallySurjective K f ∧ Presheaf.IsLocallySurjective K g) :=
  ⟨fun ⟨X, ⟨eX⟩⟩ =>
    exists_small_presentation_of_mem_essentialImage B B' h S hS hdesc' X X' eX,
    fun ⟨U, R, f, g, hf, hg⟩ =>
      mem_essentialImage_of_small_presentation B B' h S hS hdesc hdesc' X' U R f g hf hg⟩

end AlgebraicGeometry

end
