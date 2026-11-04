module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleEquivalenceRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfRepresentable

/-!
# Smoothness and étaleness of a morphism of algebraic spaces after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B` and let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S` defined using `B`. Inverse image along the
localized inclusion carries `f` to a morphism of algebraic spaces over `S` defined using `B'`.
This file shows that the image morphism is smooth as soon as `f` is, and étale as soon as `f` is.
Both are steps inside the proof that algebraicity of a stack survives a change of big site.

The mechanism is a surjective étale chart. A morphism of algebraic spaces fits in a commuting
square of étale scheme charts whose chart of the source is surjective, and both smoothness and
étaleness can be tested on such a square. The inverse image of an étale chart is an étale chart of
the inverse image: a surjective étale chart presents its target as the coequalizer of its kernel
pair, which is an étale equivalence relation, and the inverse image is a left adjoint, so it
carries that presentation to the corresponding presentation on the larger site, where the quotient
map is surjective and étale by Stacks 02WV. The scheme morphism between the two charts is the same
one, so the property it carries is unchanged.

## Main results

* `AlgebraicGeometry.changeBigSite_holdsOnSurjectiveEtaleChart`: a property of scheme morphisms
  holding on every étale chart of a morphism of algebraic spaces over `S` holds on a surjective
  étale chart of its inverse image on the larger site.
* `AlgebraicGeometry.changeBigSite_isSmooth` and `AlgebraicGeometry.changeBigSite_isEtale`:
  smoothness and étaleness of a morphism of algebraic spaces over `S` persist under enlarging the
  big fppf site.
* `AlgebraicGeometry.changeBigSiteGroupoid_isSmooth`: the inverse image of a smooth groupoid in
  algebraic spaces is a smooth groupoid in algebraic spaces.

## Implementation notes

The comparison between the inverse image of a representable sheaf and the sheaf represented by the
image of the representing object is taken in the natural form
`CategoryTheory.sheafPullback_sheafify_yoneda_natIso` of Stacks 03FP, part (1), rather than object
by object: naturality in the representing object is what transports the coequalizer square, and a
family of unrelated isomorphisms would not.

The two localized topologies are named by `AlgebraicGeometry.overTopology` rather than by
`AlgebraicGeometry.BigFppfOver.topology`, so that their underlying category is literally the domain
of `AlgebraicGeometry.inclusionOver`. The two readings agree definitionally but not at the
transparency instance search uses, so instances supplied in the second spelling are invisible to a
goal phrased in the first.

The relation used on the larger site is `AlgebraicGeometry.Space.relation` at the images of the two
projections of the kernel pair, with the roles of the two projections exchanged, since that
abbreviation takes the target map first. That its étale-equivalence-relation structure is the one
on the smaller site is a matter of definitional unfolding: the inclusion of localized big sites is
post-composition with a full subcategory inclusion, so a morphism of the smaller site and its image
have the same underlying morphism of schemes over `S`.

## References

* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
* [Stacks Project, Tag 03ZF](https://stacks.math.columbia.edu/tag/03ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

/-- A colimit-preserving functor carries a coequalizer of a pair of parallel arrows in the image of
one functor to the coequalizer of the same pair in the image of another, along a natural
isomorphism between the two composites. -/
private theorem exists_coequalizerIsoOfNatIso.{a, b, c, d, e, f} {C : Type a} [Category.{b} C]
    {A : Type c} [Category.{d} A] {B : Type e} [Category.{f} B]
    (Y : C ⥤ A) (Z : C ⥤ B) (L : A ⥤ B) (e : Y ⋙ L ≅ Z)
    {R U : C} (s t : R ⟶ U) {F : A} {G : B}
    (q : Y.obj U ⟶ F) (wq : Y.map s ≫ q = Y.map t ≫ q)
    (q' : Z.obj U ⟶ G) (wq' : Z.map s ≫ q' = Z.map t ≫ q')
    (hq : IsColimit (Cofork.ofπ q wq)) (hq' : IsColimit (Cofork.ofπ q' wq'))
    [PreservesColimit (parallelPair (Y.map s) (Y.map t)) L] :
    ∃ e' : L.obj F ≅ G, (e.app U).inv ≫ L.map q ≫ e'.hom = q' := by
  let c : Cofork (Z.map s) (Z.map t) := Cofork.ofπ ((e.app U).inv ≫ L.map q) (by
    have hs := e.inv.naturality s
    have ht := e.inv.naturality t
    dsimp at hs ht
    change Z.map s ≫ e.inv.app U ≫ L.map q = Z.map t ≫ e.inv.app U ≫ L.map q
    rw [← Category.assoc, hs, ← Category.assoc, ht]
    simp only [Category.assoc, ← L.map_comp, wq])
  have hc : IsColimit c := Cofork.isColimitOfIsos
    (Cofork.ofπ (L.map q) (by simp only [← L.map_comp, wq]))
    (isColimitCoforkMapOfIsColimit L wq hq) c
    (e.app R) (e.app U) (Iso.refl _) (e.hom.naturality s).symm
    (e.hom.naturality t).symm (by simp [c])
  refine ⟨hc.coconePointUniqueUpToIso hq', ?_⟩
  simpa [c] using hc.comp_coconePointUniqueUpToIso_hom hq' WalkingParallelPair.one

/-- A morphism property which respects isomorphisms is unchanged by post-composing with an
isomorphism. The hypothesis is an explicit argument, so that it can be supplied where instance
search cannot see it. -/
private theorem comp_iso_of_respectsIso.{a, b} {C : Type a} [Category.{b} C]
    (P : MorphismProperty C) (hP : P.RespectsIso) {X Y Z : C} (α : Y ≅ Z) (f : X ⟶ Y)
    (hf : P f) : P (f ≫ α.hom) :=
  @MorphismProperty.RespectsIso.postcomp _ _ P hP _ _ _ α.hom
    ⟨⟨α.inv, α.hom_inv_id, α.inv_hom_id⟩⟩ f hf

/-- A morphism of algebraic spaces over `S` fits in a commuting square of étale scheme charts
whose chart of the source is surjective and whose chart of the target is surjective as well. -/
private theorem exists_surjective_etale_chart_square (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
      p ≫ f = yoneda.map a ≫ q ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q := by
  have hbcSurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbcEtale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  obtain ⟨V, q, hqs, hqe⟩ := hY.exists_atlas
  have hP := isAlgebraicSpace_pullback B S hS f q hX
    (isAlgebraicSpace_yoneda B S hS V) hY
  obtain ⟨U, r, hrs, hre⟩ := hP.exists_atlas
  refine ⟨U, V, r ≫ pullback.fst f q, q, yoneda.preimage (r ≫ pullback.snd f q), ?_, ?_, ?_,
    hqs, hqe⟩
  · rw [yoneda.map_preimage, Category.assoc, Category.assoc, pullback.condition]
  · exact MorphismProperty.comp_mem _ _ _ hrs (MorphismProperty.pullback_fst f q hqs)
  · exact MorphismProperty.comp_mem _ _ _ hre (MorphismProperty.pullback_fst f q hqe)

/-- The inverse image of a surjective étale chart of an algebraic space over `S` is a surjective
étale chart of the inverse-image algebraic space.

The chart presents its target as the coequalizer of its kernel pair, an étale equivalence relation;
the inverse image preserves that coequalizer, and on the larger site the quotient map of the image
relation is surjective and étale by Stacks 02WV. -/
private theorem map_surjective_etale_atlas (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    [(overTopology .fppf B S hS).Subcanonical]
    [(overTopology .fppf B' S (largerContains h hS)).Subcanonical]
    (L : Sheaf (overTopology .fppf B S hS) (Type u) ⥤
      Sheaf (overTopology .fppf B' S (largerContains h hS)) (Type u))
    [PreservesColimits L]
    (e : (overTopology .fppf B S hS).yoneda ⋙ L ≅
      inclusionOver h S hS ⋙ (overTopology .fppf B' S (largerContains h hS)).yoneda)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    let q' := (e.app U).inv.hom ≫
      (L.map (show (overTopology .fppf B S hS).yoneda.obj U ⟶
        (⟨F, hF.isSheaf⟩ : Sheaf _ (Type u)) from ⟨q⟩)).hom
    (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf q' ∧
    (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf q' := by
  let sheafifyLarge : HasSheafify (BigFppfOver.topology B' S (largerContains h hS)) (Type u) :=
    BigFppfOver.hasSheafify_type B' S (largerContains h hS)
  let R := hqe.rep.pullback q
  let s : R ⟶ U := hqe.rep.fst' q
  let t : R ⟶ U := hqe.rep.snd q
  let si : (inclusionOver h S hS).obj R ⟶ (inclusionOver h S hS).obj U :=
    (inclusionOver h S hS).map s
  let ti : (inclusionOver h S hS).obj R ⟶ (inclusionOver h S hS).obj U :=
    (inclusionOver h S hS).map t
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := hqe.rep.isPullback' q
  have hs : Etale ((Over.post B.inclusion).map s).left :=
    hqe.property q (yoneda.map t) s hR.flip
  have ht : Etale ((Over.post B.inclusion).map t).left :=
    hqe.property q (yoneda.map s) t hR
  have hrel : Stacks.Groupoids.IsEtaleEquivalenceRelation (Space.relation B S hS t s) :=
    { isEquivalenceRelation := by
        simpa only [Space.relation, Stacks.Groupoids.PreRelation.target,
          Stacks.Groupoids.PreRelation.source, prod.lift_fst, prod.lift_snd]
          using Space.isEquivalenceRelation_of_isPullback B S hS q s t hR
      etale_source := by
        simpa only [Space.relation, Stacks.Groupoids.PreRelation.source, prod.lift_snd]
          using ht
      etale_target := by
        simpa only [Space.relation, Stacks.Groupoids.PreRelation.target, prod.lift_fst]
          using hs }
  have hrel' : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (Space.relation B' S (largerContains h hS) ti si) :=
    inferInstanceAs (Stacks.Groupoids.IsEtaleEquivalenceRelation (Space.relation B S hS t s))
  have hQ : IsAlgebraicSpace B' S (largerContains h hS)
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B' S (largerContains h hS))
        (Over.post B'.inclusion)
        (Space.relation B' S (largerContains h hS) ti si)).obj :=
    Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B' S (largerContains h hS)
      ti si (descentForQuotients B' S (largerContains h hS))
  let q' := Space.quotientMap B' S (largerContains h hS) ti si
  have hrep' := Space.relativelyRepresentable_quotientMap_of_isAlgebraicSpace B' S
    (largerContains h hS) ti si hQ
  have hqs' := Space.quotientMap_surjective B' S (largerContains h hS) ti si hrep'
  have hqe' := Space.quotientMap_etale B' S (largerContains h hS) ti si hrep'
  have hR' : IsPullback (yoneda.map si) (yoneda.map ti) q' q' :=
    Space.quotientMap_isPullback B' S (largerContains h hS) ti si
  obtain ⟨_, _, ⟨hq⟩⟩ := Space.isCoequalizer_of_surjectiveEtale B S hS q s t hR hF hqs hqe
  obtain ⟨_, _, ⟨hq'⟩⟩ := Space.isCoequalizer_of_surjectiveEtale B' S (largerContains h hS)
    q' si ti hR' hQ hqs' hqe'
  obtain ⟨e', he'⟩ := exists_coequalizerIsoOfNatIso (overTopology .fppf B S hS).yoneda
    ((inclusionOver h S hS) ⋙ (overTopology .fppf B' S (largerContains h hS)).yoneda) L e s t
    ((⟨q⟩ : (overTopology .fppf B S hS).yoneda.obj U ⟶
      (⟨F, hF.isSheaf⟩ : Sheaf (overTopology .fppf B S hS) (Type u))))
    (Sheaf.hom_ext hR.w)
    ((⟨q'⟩ : ((inclusionOver h S hS) ⋙
      (overTopology .fppf B' S (largerContains h hS)).yoneda).obj U ⟶
      (⟨_, hQ.isSheaf⟩ : Sheaf (overTopology .fppf B' S (largerContains h hS)) (Type u))))
    (Sheaf.hom_ext hR'.w) hq hq'
  have he0 : (e.app U).inv ≫ L.map ((⟨q⟩ : (overTopology .fppf B S hS).yoneda.obj U ⟶
      (⟨F, hF.isSheaf⟩ : Sheaf (overTopology .fppf B S hS) (Type u)))) =
      (⟨q'⟩ : ((inclusionOver h S hS) ⋙
        (overTopology .fppf B' S (largerContains h hS)).yoneda).obj U ⟶
        (⟨_, hQ.isSheaf⟩ : Sheaf (overTopology .fppf B' S (largerContains h hS))
          (Type u))) ≫ e'.inv := by
    rw [← he']
    simp
  have he := congrArg (fun k => k.hom) he0
  have key : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      (g : yoneda.obj ((inclusionOver h S hS).obj U) ⟶
        (L.obj (⟨F, hF.isSheaf⟩ : Sheaf (overTopology .fppf B S hS) (Type u))).obj),
      g = q' ≫ e'.inv.hom →
      (MorphismProperty.inverseImage P
        (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf q' →
      (MorphismProperty.inverseImage P
        (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf g := by
    rintro P _ g rfl hq
    exact comp_iso_of_respectsIso _
      (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso
      ((sheafToPresheaf (overTopology .fppf B' S (largerContains h hS)) (Type u)).mapIso
        e'.symm) q' hq
  exact ⟨key _ _ he hqs', key _ _ he hqe'⟩

/-- **A square of étale charts of a morphism of algebraic spaces, and its inverse image.** A
morphism `f` of algebraic spaces over `S` has a commuting square of étale charts whose chart of the
source is surjective, over a morphism `a` of the site, whose inverse image is a commuting square of
étale charts of the inverse image of `f`, over the image of `a`, again with surjective chart of the
source. The two squares have the same morphism of schemes between their charts. -/
private theorem exists_changeBigSite_etaleChartSquare (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.obj) (q : yoneda.obj V ⟶ Y.obj)
      (a : U ⟶ V),
      (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      yoneda.map a ≫ q = p ≫ f.hom ∧
      ∃ (p' : yoneda.obj ((inclusionOver h S hS).obj U) ⟶
          ((changeBigSite B B' h S hS).obj X).obj)
        (q' : yoneda.obj ((inclusionOver h S hS).obj V) ⟶
          ((changeBigSite B B' h S hS).obj Y).obj),
        (MorphismProperty.inverseImage (@Etale.{u})
          (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf p' ∧
        (MorphismProperty.inverseImage (@Etale.{u})
          (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf q' ∧
        (MorphismProperty.inverseImage (@Surjective.{u})
          (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf p' ∧
        yoneda.map ((inclusionOver h S hS).map a) ≫ q' =
          p' ≫ ((changeBigSite B B' h S hS).map f).hom := by
  have hcont : (inclusionOver h S hS).IsContinuous (overTopology .fppf B S hS)
      (overTopology .fppf B' S (largerContains h hS)) :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  have hadj : ((inclusionOver h S hS).sheafPushforwardContinuous (Type u)
      (overTopology .fppf B S hS)
      (overTopology .fppf B' S (largerContains h hS))).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let sheafifyJ : HasSheafify (overTopology .fppf B S hS) (Type u) :=
    BigFppfOver.hasSheafify_type B S hS
  let sheafifyK : HasSheafify (overTopology .fppf B' S (largerContains h hS)) (Type u) :=
    BigFppfOver.hasSheafify_type B' S (largerContains h hS)
  have hsubJ : (overTopology .fppf B S hS).Subcanonical :=
    .of_isSheaf_yoneda_obj _ fun Z =>
      (isSheaf_iff_isSheaf_of_type _ _).mp (isAlgebraicSpace_yoneda B S hS Z).isSheaf
  have hsubK : (overTopology .fppf B' S (largerContains h hS)).Subcanonical :=
    .of_isSheaf_yoneda_obj _ fun Z =>
      (isSheaf_iff_isSheaf_of_type _ _).mp
        (isAlgebraicSpace_yoneda B' S (largerContains h hS) Z).isSheaf
  let L := (inclusionOver h S hS).sheafPullback (Type u) (overTopology .fppf B S hS)
    (overTopology .fppf B' S (largerContains h hS))
  have hcolim : PreservesColimits L :=
    ((inclusionOver h S hS).sheafAdjunctionContinuous (Type u) (overTopology .fppf B S hS)
      (overTopology .fppf B' S (largerContains h hS))).leftAdjoint_preservesColimits
  let e := pullbackYonedaIso (inclusionOver h S hS) (overTopology .fppf B S hS)
    (overTopology .fppf B' S (largerContains h hS))
  obtain ⟨U, V, p, q, a, hw, hps, hpe, hqs, hqe⟩ :=
    exists_surjective_etale_chart_square B S hS X.property Y.property f.hom
  let psh : (overTopology .fppf B S hS).yoneda.obj U ⟶
    (⟨X.obj, X.property.isSheaf⟩ : Sheaf (overTopology .fppf B S hS) (Type u)) := ⟨p⟩
  let qsh : (overTopology .fppf B S hS).yoneda.obj V ⟶
    (⟨Y.obj, Y.property.isSheaf⟩ : Sheaf (overTopology .fppf B S hS) (Type u)) := ⟨q⟩
  let fsh : (⟨X.obj, X.property.isSheaf⟩ : Sheaf (overTopology .fppf B S hS) (Type u)) ⟶
      ⟨Y.obj, Y.property.isSheaf⟩ := ⟨f.hom⟩
  obtain ⟨hps', hpe'⟩ := map_surjective_etale_atlas B B' h S hS L e X.property p hps hpe
  obtain ⟨_, hqe'⟩ := map_surjective_etale_atlas B B' h S hS L e Y.property q hqs hqe
  refine ⟨U, V, p, q, a, hpe, hqe, hps, hw.symm, (e.app U).inv.hom ≫ (L.map psh).hom,
    (e.app V).inv.hom ≫ (L.map qsh).hom, hpe', hqe', hps', ?_⟩
  · have hwsh : psh ≫ fsh = (overTopology .fppf B S hS).yoneda.map a ≫ qsh :=
      Sheaf.hom_ext hw
    have hn : ((inclusionOver h S hS) ⋙
          (overTopology .fppf B' S (largerContains h hS)).yoneda).map a ≫ (e.app V).inv =
        (e.app U).inv ≫ L.map ((overTopology .fppf B S hS).yoneda.map a) :=
      e.inv.naturality a
    have hh : ((inclusionOver h S hS) ⋙
          (overTopology .fppf B' S (largerContains h hS)).yoneda).map a ≫
            (e.app V).inv ≫ L.map qsh =
        (e.app U).inv ≫ L.map psh ≫ L.map fsh := by
      rw [← Category.assoc, hn, Category.assoc, ← L.map_comp, ← hwsh, L.map_comp]
    exact congrArg (fun k => k.hom) hh

/-- **A property of scheme morphisms holding on every étale chart of a morphism of algebraic
spaces holds on a surjective étale chart of its inverse image.** The inverse images of a commuting
square of étale charts of `f` form a commuting square of étale charts of the inverse image of `f`,
with the same morphism of schemes between the charts; the chart of the source stays surjective. -/
theorem changeBigSite_holdsOnSurjectiveEtaleChart (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (P : MorphismProperty Scheme.{u})
    (hf : Space.HoldsOnEveryEtaleChart B S hS P f.hom) :
    Space.HoldsOnSurjectiveEtaleChart B' S (largerContains h hS) P
      ((changeBigSite B B' h S hS).map f).hom := by
  obtain ⟨U, V, p, q, a, hpe, hqe, -, hw, p', q', hpe', hqe', hps', hw'⟩ :=
    exists_changeBigSite_etaleChartSquare B B' h S hS f
  exact ⟨_, _, p', q', _, hpe', hqe', hps', hw', hf U V p q a hpe hqe hw⟩

/-- **A property of scheme morphisms holding on every étale chart of the inverse image of a
morphism of algebraic spaces holds on a surjective étale chart of the morphism itself.** The
inverse image of a commuting square of étale charts of `f`, with surjective chart of the source,
is a commuting square of étale charts of the inverse image of `f`, with the same morphism of
schemes between the charts. -/
theorem holdsOnSurjectiveEtaleChart_of_changeBigSite (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (P : MorphismProperty Scheme.{u})
    (hf : Space.HoldsOnEveryEtaleChart B' S (largerContains h hS) P
      ((changeBigSite B B' h S hS).map f).hom) :
    Space.HoldsOnSurjectiveEtaleChart B S hS P f.hom := by
  obtain ⟨U, V, p, q, a, hpe, hqe, hps, hw, p', q', hpe', hqe', -, hw'⟩ :=
    exists_changeBigSite_etaleChartSquare B B' h S hS f
  exact ⟨U, V, p, q, a, hpe, hqe, hps, hw, hf _ _ p' q' _ hpe' hqe' hw'⟩

/-- **Smoothness of a morphism of algebraic spaces over `S` persists under enlarging the big fppf
site.** -/
theorem changeBigSite_isSmooth (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B')
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.IsSmooth B S hS f.hom) :
    Space.IsSmooth B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom :=
  ((Space.isSmooth_tfae B' S (largerContains h hS)
    ((changeBigSite B B' h S hS).obj X).property
    ((changeBigSite B B' h S hS).obj Y).property
    ((changeBigSite B B' h S hS).map f).hom).out 8 1).mp
      (changeBigSite_holdsOnSurjectiveEtaleChart B B' h S hS f _ hf)

/-- **Smoothness of a morphism of algebraic spaces over `S` descends from the enlarged big fppf
site**: if the inverse image of `f` is smooth, so is `f`. The inverse image of a square of étale
charts of `f`, with surjective chart of the source, is a square of étale charts of the inverse
image with the same morphism of schemes between the charts, and smoothness of the inverse image
holds on every such square. -/
theorem isSmooth_of_changeBigSite_isSmooth (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.IsSmooth B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom) :
    Space.IsSmooth B S hS f.hom :=
  ((Space.isSmooth_tfae B S hS X.property Y.property f.hom).out 8 1).mp
    (holdsOnSurjectiveEtaleChart_of_changeBigSite B B' h S hS f _
      (((Space.isSmooth_tfae B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).property
        ((changeBigSite B B' h S hS).obj Y).property
        ((changeBigSite B B' h S hS).map f).hom).out 1 7).mp hf))

/-- **Étaleness of a morphism of algebraic spaces over `S` persists under enlarging the big fppf
site.** -/
theorem changeBigSite_isEtale (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B')
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.IsEtale B S hS f.hom) :
    Space.IsEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom := by
  obtain ⟨U, V, p, q, a, hp, hq, hps, hw, ha⟩ :=
    changeBigSite_holdsOnSurjectiveEtaleChart B B' h S hS f _
      ((Space.isEtale_iff_holdsOnEveryEtaleChart B S hS X.property Y.property f.hom).mp hf)
  exact (Space.isEtale_iff_exists_etale_chart_square B' S (largerContains h hS)
    ((changeBigSite B B' h S hS).obj X).property
    ((changeBigSite B B' h S hS).obj Y).property
    ((changeBigSite B B' h S hS).map f).hom).mpr
      ⟨U, V, p, q, a, hw.symm, hps, hp, hq, ha⟩

/-- **The inverse image of a smooth groupoid in algebraic spaces is smooth.** The source and target
maps of the inverse-image groupoid are the inverse images of those of the given one. -/
theorem changeBigSiteGroupoid_isSmooth (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    {Bs : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Bs)
    (hG : GroupoidInAlgebraicSpaces.IsSmooth B S hS G) :
    GroupoidInAlgebraicSpaces.IsSmooth B' S (largerContains h hS)
      (changeBigSiteGroupoid B B' h S hS G) :=
  ⟨changeBigSite_isSmooth B B' h S hS G.source hG.source,
    changeBigSite_isSmooth B B' h S hS G.target hG.target⟩

/-- **A groupoid in algebraic spaces whose inverse image is smooth is smooth.** The source and
target maps of the inverse-image groupoid are the inverse images of those of the given one, and
smoothness descends from the enlarged site. -/
theorem isSmooth_of_changeBigSiteGroupoid_isSmooth (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    {Bs : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Bs)
    (hG : GroupoidInAlgebraicSpaces.IsSmooth B' S (largerContains h hS)
      (changeBigSiteGroupoid B B' h S hS G)) :
    GroupoidInAlgebraicSpaces.IsSmooth B S hS G :=
  ⟨isSmooth_of_changeBigSite_isSmooth B B' h S hS G.source hG.source,
    isSmooth_of_changeBigSite_isSmooth B B' h S hS G.target hG.target⟩

end AlgebraicGeometry

end
