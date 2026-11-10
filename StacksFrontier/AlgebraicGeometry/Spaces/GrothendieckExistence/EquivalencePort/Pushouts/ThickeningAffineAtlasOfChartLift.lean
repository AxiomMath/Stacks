module

public import StacksFrontier.AlgebraicGeometry.C1573Port.Pushout.ThickeningAffineGluingRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.BaseAdditions.ThickeningAffineSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Slice
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# From a lifted étale chart to a compatible pair of charts

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces over
`S`.  The proof of [Stacks Project, Tag 07VX] chooses a surjective étale chart `V ⟶ Y`, sets
`U = V ×_Y X`, lifts the étale chart `U ⟶ X` across the thickening to an étale `U' ⟶ X'` with
`U = U' ×_{X'} X` ([Stacks Project, Tag 05ZS]), and then forms the pushouts `P = U' ⨿_U V` and
`Rel = (U' ×_{X'} U') ⨿_{U ×_X U} (V ×_Y V)` of schemes, which carry an étale equivalence relation
`Rel ⇉ P` whose quotient is the pushout of algebraic spaces.

This file carries out every step of that paragraph after the lift: from the two cartesian squares
`U = V ×_Y X` and `U = U' ×_{X'} X` it builds the kernel pairs, the two scheme pushouts inside the
big fppf site, the two projections `Rel ⇉ P`, and proves that they form an étale equivalence
relation — the part whose details the source omits.  The result is a
`AlgebraicGeometry.Space.ThickeningAffineAtlas`, so the pushout of algebraic spaces exists and
`Y ⟶ Y'` is a thickening (`AlgebraicGeometry.Space.isPushout_quotient_of_thickeningAffineAtlas`).

## Main results

* `AlgebraicGeometry.Space.C1573.exists_isPushout_toScheme_of_isThickening`: the pushout of
  schemes of a thickening and an affine morphism between objects of the big fppf site of `S` is
  again an object of the site.
* `AlgebraicGeometry.Space.C1573.exists_isPullback_kernelPair_comparison`: the comparison between
  the kernel pairs of two charts related by a cartesian square, with its two cartesian squares.
* `AlgebraicGeometry.Space.C1573.nonempty_thickeningAffineAtlas_of_isPullback`: a surjective
  étale chart of `Y`, an étale chart of `X'` and the two cartesian squares of the lift produce a
  `AlgebraicGeometry.Space.ThickeningAffineAtlas`.
* `AlgebraicGeometry.Space.C1573.hasPushout_of_isPullback_chart` and
  `AlgebraicGeometry.Space.C1573.pushout_inr_isThickening_of_isPullback_chart`: such a span has a
  pushout of algebraic spaces, and `Y ⟶ Y'` is a thickening.
* `AlgebraicGeometry.Space.C1573.hasThickeningAffineAtlases_of_forall_chartLift`: when every such
  span admits a lifted chart, every one of them admits a compatible pair of charts, which is the
  hypothesis of `AlgebraicGeometry.Space.hasPushout_of_isThickening_of_isAffineHom` and
  `AlgebraicGeometry.Space.pushout_inr_isThickening`.

## Implementation notes

Stacks 07VX is not registered here: the lift of the chart, Stacks 05ZS on the small étale sites,
is an input of the main theorem, in the form of its two cartesian squares.  The étale equivalence
relation is `Stacks.Pushout.C1573.isEquivalenceRelation_of_isPushout`, a statement about schemes;
it is transported to the slice over `S` through `CategoryTheory.isEquivalenceRelation_of_left`.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfOver.hasSheafify_type

/-- **A pushout of schemes along a thickening stays in the big fppf site.**  For objects of the
big fppf site of `S`, a thickening `k : Z ⟶ Z'` and an affine morphism `g : Z ⟶ W`, the pushout
`Z' ⨿_Z W` of schemes ([Stacks Project, Tag 07RT]) is no bigger than `Z'` and `W`, so it is again
an object of the site, with its structure morphism to `S` induced by those of `Z'` and `W`. -/
theorem C1573.exists_isPushout_toScheme_of_isThickening {Z Z' W : BigFppfOver B S hS} (k : Z ⟶ Z')
    (g : Z ⟶ W) (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g)] :
    ∃ (P : BigFppfOver B S hS) (a : Z' ⟶ P) (b : W ⟶ P),
      IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) := by
  let Φ := BigFppfOver.toScheme B S hS
  have : HasPushout (Φ.map k) (Φ.map g) :=
    Stacks.Pushout.hasPushout_of_isThickening_of_isAffineHom' _ _ hk
  have hpo := IsPushout.of_hasPushout (Φ.map k) (Φ.map g)
  have hsize : B.Contains (pushout (Φ.map k) (Φ.map g)) :=
    (Stacks.Pushout.C1573.size_le_of_isPushout hk hpo).trans_lt
      (max_lt Z'.left.property W.left.property)
  have hw : Φ.map k ≫ B.inclusion.map Z'.hom = Φ.map g ≫ B.inclusion.map W.hom := by
    change B.inclusion.map k.left ≫ B.inclusion.map Z'.hom =
      B.inclusion.map g.left ≫ B.inclusion.map W.hom
    rw [← Functor.map_comp, ← Functor.map_comp, Over.w k, Over.w g]
  let σ := pushout.desc (B.inclusion.map Z'.hom) (B.inclusion.map W.hom) hw
  exact ⟨BigFppfOver.mk B S hS hsize σ,
    BigFppfOver.homMk B S hS hsize σ (pushout.inl _ _) (pushout.inl_desc _ _ _),
    BigFppfOver.homMk B S hS hsize σ (pushout.inr _ _) (pushout.inr_desc _ _ _), hpo⟩

/-- **Comparing the kernel pairs of two charts.**  Let `p : U ⟶ F` and `p' : U' ⟶ G` be charts
by objects of the big fppf site with kernel pairs `R₀` and `R'`, and let the square
`U ⟶ U'` over `φ : F ⟶ G` be cartesian.  The induced map `R₀ ⟶ R'` makes both squares over
`k : U ⟶ U'`, on the first and on the second projections, cartesian. -/
theorem C1573.exists_isPullback_kernelPair_comparison
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U U' R₀ R' : BigFppfOver B S hS}
    {p : yoneda.obj U ⟶ F} {p' : yoneda.obj U' ⟶ G} {φ : F ⟶ G} {k : U ⟶ U'}
    (hpb : IsPullback (yoneda.map k) p p' φ)
    {s₀ t₀ : R₀ ⟶ U} (h₀ : IsPullback (yoneda.map s₀) (yoneda.map t₀) p p)
    {s' t' : R' ⟶ U'} (h' : IsPullback (yoneda.map s') (yoneda.map t') p' p') :
    ∃ kR : R₀ ⟶ R', kR ≫ s' = s₀ ≫ k ∧ kR ≫ t' = t₀ ≫ k ∧
      IsPullback (yoneda.map kR) (yoneda.map s₀) (yoneda.map s') (yoneda.map k) ∧
      IsPullback (yoneda.map kR) (yoneda.map t₀) (yoneda.map t') (yoneda.map k) := by
  have hw : yoneda.map (s₀ ≫ k) ≫ p' = yoneda.map (t₀ ≫ k) ≫ p' := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hpb.w,
      ← Category.assoc, h₀.w, Category.assoc]
  let kR : R₀ ⟶ R' := yoneda.preimage (h'.lift _ _ hw)
  have hkR : yoneda.map kR = h'.lift _ _ hw := Functor.map_preimage _ _
  have hs : yoneda.map kR ≫ yoneda.map s' = yoneda.map s₀ ≫ yoneda.map k := by
    rw [hkR, h'.lift_fst, Functor.map_comp]
  have ht : yoneda.map kR ≫ yoneda.map t' = yoneda.map t₀ ≫ yoneda.map k := by
    rw [hkR, h'.lift_snd, Functor.map_comp]
  refine ⟨kR, yoneda.map_injective (by simpa only [Functor.map_comp] using hs),
    yoneda.map_injective (by simpa only [Functor.map_comp] using ht), ?_, ?_⟩
  · have hbig := h₀.flip.paste_horiz hpb
    rw [← ht, ← hpb.w] at hbig
    exact IsPullback.of_right hbig hs h'.flip
  · have hbig := h₀.paste_horiz hpb
    rw [← hs, ← hpb.w] at hbig
    exact IsPullback.of_right hbig ht h'

/-- **The compatible pair of charts of [Stacks Project, Tag 07VX], from a lifted chart, with its
kernel-pair data.** The atlas of `nonempty_thickeningAffineAtlas_of_isPullback`, together with the
kernel pair `s₀, t₀` of the chart of `X` and the two cartesian squares exhibiting it as the base
change of the kernel pairs of the charts of `X'` and of `Y` along the first projections. -/
theorem C1573.exists_thickeningAffineAtlas_of_isPullback
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {U U' V : BigFppfOver B S hS} (q : yoneda.obj V ⟶ Y.1) (p : yoneda.obj U ⟶ X.1)
    (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U') (g : U ⟶ V)
    (hqS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hp'E : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p')
    (hpbf : IsPullback p (yoneda.map g) f.hom q)
    (hpbi : IsPullback (yoneda.map k) p p' i.hom) :
    ∃ (A : ThickeningAffineAtlas B S hS i f) (s₀ t₀ : A.R₀ ⟶ A.U),
      IsPullback (yoneda.map s₀) (yoneda.map t₀) A.p A.p ∧
      A.kR ≫ A.s' = s₀ ≫ A.k ∧ A.gR ≫ A.sY = s₀ ≫ A.g ∧
      IsPullback ((BigFppfOver.toScheme B S hS).map A.kR) ((BigFppfOver.toScheme B S hS).map s₀)
        ((BigFppfOver.toScheme B S hS).map A.s') ((BigFppfOver.toScheme B S hS).map A.k) ∧
      IsPullback ((BigFppfOver.toScheme B S hS).map A.gR) ((BigFppfOver.toScheme B S hS).map s₀)
        ((BigFppfOver.toScheme B S hS).map A.sY) ((BigFppfOver.toScheme B S hS).map A.g) ∧
      ∃ (hU : A.U = U) (hU' : A.U' = U') (hV : A.V = V),
        A.p = yoneda.map (eqToHom hU) ≫ p ∧ A.p' = yoneda.map (eqToHom hU') ≫ p' ∧
        A.q = yoneda.map (eqToHom hV) ≫ q ∧ A.k = eqToHom hU ≫ k ≫ eqToHom hU'.symm ∧
        A.g = eqToHom hU ≫ g ≫ eqToHom hV.symm := by
  let Φ := BigFppfOver.toScheme B S hS
  have hstabE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) Φ)).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hstabS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        Φ)).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  -- the chart of `X`
  have hpE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) Φ)) p :=
    MorphismProperty.of_isPullback hpbf.flip hqE
  have hpS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) Φ)) p :=
    MorphismProperty.of_isPullback hpbf.flip hqS
  -- the chart of `X'` is surjective, because the chart of `X` and the thickening are
  have hp'S : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) Φ)) p' := by
    refine (presheafSurjective_iff_isSurjective_yoneda B S hS X'.1 X'.property U' p').2 ?_
    have hpPts := (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.property U p).1 hpS
    intro x
    obtain ⟨y, rfl⟩ := hi.surjective_pointsMap x
    obtain ⟨z, rfl⟩ := hpPts y
    refine ⟨pointsMap B S hS _ (yoneda.map k) z, ?_⟩
    have h := congrFun (pointsMap_comp B S hS _ (yoneda.map k) p') z
    have h' := congrFun (pointsMap_comp B S hS _ p i.hom) z
    simp only [Function.comp_apply] at h h'
    rw [← h, ← h', hpbi.w]
  -- the two morphisms of charts
  have hk : Stacks.Thickenings.IsThickening (Φ.map k) :=
    ⟨hi.isClosedImmersion.property p' p k hpbi.flip,
      (hi.surjective.property p' p k hpbi.flip).surj⟩
  have hgA : _root_.AlgebraicGeometry.IsAffineHom (Φ.map g) :=
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.property Y.property
      hf).2.property q p g hpbf
  -- the kernel pairs
  obtain ⟨TY, sY, tY, hTY⟩ : ∃ (R : BigFppfOver B S hS) (s t : R ⟶ V),
      IsPullback (yoneda.map s) (yoneda.map t) q q :=
    ⟨hqE.rep.pullback q, hqE.rep.fst' q, hqE.rep.snd q, hqE.rep.isPullback' q⟩
  obtain ⟨R', s', t', hR'⟩ : ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U'),
      IsPullback (yoneda.map s) (yoneda.map t) p' p' :=
    ⟨hp'E.rep.pullback p', hp'E.rep.fst' p', hp'E.rep.snd p', hp'E.rep.isPullback' p'⟩
  obtain ⟨R₀, s₀, t₀, hR₀⟩ : ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) p p :=
    ⟨hpE.rep.pullback p, hpE.rep.fst' p, hpE.rep.snd p, hpE.rep.isPullback' p⟩
  obtain ⟨kR, hkRs, hkRt, hk₁, hk₂⟩ :=
    exists_isPullback_kernelPair_comparison B S hS hpbi hR₀ hR'
  obtain ⟨gR, hgRs, hgRt, hg₁, hg₂⟩ :=
    exists_isPullback_kernelPair_comparison B S hS hpbf.flip hR₀ hTY
  have hK₁ := (IsPullback.of_map_of_faithful yoneda hk₁).map Φ
  have hK₂ := (IsPullback.of_map_of_faithful yoneda hk₂).map Φ
  have hG₁ := (IsPullback.of_map_of_faithful yoneda hg₁).map Φ
  have hG₂ := (IsPullback.of_map_of_faithful yoneda hg₂).map Φ
  have hkR : Stacks.Thickenings.IsThickening (Φ.map kR) :=
    Stacks.Thickenings.isThickening_of_isPullback hK₁ hk
  have hgRA : _root_.AlgebraicGeometry.IsAffineHom (Φ.map gR) :=
    MorphismProperty.of_isPullback hG₁.flip hgA
  -- the two pushouts of schemes, in the site
  obtain ⟨P, a, b, hPush⟩ := exists_isPushout_toScheme_of_isThickening B S hS k g hk
  obtain ⟨Rel, aR, bR, hRelPush⟩ := exists_isPushout_toScheme_of_isThickening B S hS kR gR hkR
  have hPs : IsPushout k g a b := IsPushout.of_map_of_faithful Φ hPush
  have hRs : IsPushout kR gR aR bR := IsPushout.of_map_of_faithful Φ hRelPush
  -- the two projections of the relation
  let s : Rel ⟶ P := hRs.desc (s' ≫ a) (sY ≫ b) (by
    rw [reassoc_of% hkRs, reassoc_of% hgRs, hPs.w])
  let t : Rel ⟶ P := hRs.desc (t' ≫ a) (tY ≫ b) (by
    rw [reassoc_of% hkRt, reassoc_of% hgRt, hPs.w])
  have has : aR ≫ s = s' ≫ a := hRs.inl_desc _ _ _
  have hbs : bR ≫ s = sY ≫ b := hRs.inr_desc _ _ _
  have hat : aR ≫ t = t' ≫ a := hRs.inl_desc _ _ _
  have hbt : bR ≫ t = tY ≫ b := hRs.inr_desc _ _ _
  -- the étale equivalence relations of the two charts, read as schemes
  have : Etale (Φ.map s') := hp'E.property p' (yoneda.map t') s' hR'.flip
  have : Etale (Φ.map t') := hp'E.property p' (yoneda.map s') t' hR'
  have : Etale (Φ.map sY) := hqE.property q (yoneda.map tY) sY hTY.flip
  have : Etale (Φ.map tY) := hqE.property q (yoneda.map sY) tY hTY
  have eR : IsEquivalenceRelation (Φ.map t') (Φ.map s') :=
    isEquivalenceRelation_left _ _ (isEquivalenceRelation_of_isPullback B S hS p' t' s' hR'.flip)
  have eT : IsEquivalenceRelation (Φ.map tY) (Φ.map sY) :=
    isEquivalenceRelation_left _ _ (isEquivalenceRelation_of_isPullback B S hS q tY sY hTY.flip)
  obtain ⟨hEq, hEs, hEt⟩ := Stacks.Pushout.C1573.isEquivalenceRelation_of_isPushout
    hk hPush hRelPush hK₁ hK₂ hG₁ hG₂ eR eT
    (by rw [← Φ.map_comp, ← Φ.map_comp, has]) (by rw [← Φ.map_comp, ← Φ.map_comp, hat])
    (by rw [← Φ.map_comp, ← Φ.map_comp, hbs]) (by rw [← Φ.map_comp, ← Φ.map_comp, hbt])
  have hsrc : (relation B S hS s t).source = (Over.post B.inclusion).map s := prod.lift_snd _ _
  have htgt : (relation B S hS s t).target = (Over.post B.inclusion).map t := prod.lift_fst _ _
  have hrel : IsEtaleEquivalenceRelation (relation B S hS s t) := by
    have h₁ : IsEquivalenceRelation (relation B S hS s t).target
        (relation B S hS s t).source := by
      rw [htgt, hsrc]
      exact isEquivalenceRelation_of_left (h := hEq) _ _
    have h₂ : Etale (relation B S hS s t).source.left := by
      rw [hsrc]
      exact hEs
    have h₃ : Etale (relation B S hS s t).target.left := by
      rw [htgt]
      exact hEt
    exact ⟨⟩
  refine ⟨{
    U := U
    U' := U'
    V := V
    R₀ := R₀
    R' := R'
    T := TY
    P := P
    Rel := Rel
    p := p
    p' := p'
    q := q
    k := k
    g := g
    kR := kR
    gR := gR
    s' := s'
    t' := t'
    sY := sY
    tY := tY
    a := a
    b := b
    aR := aR
    bR := bR
    s := s
    t := t
    isPullback_affine := hpbf
    isPullback_thickening := hpbi
    isThickening_k := hk
    isAffineHom_g := hgA
    isThickening_kR := hkR
    isAffineHom_gR := hgRA
    surjective_p := hpS
    etale_p := hpE
    surjective_p' := hp'S
    etale_p' := hp'E
    surjective_q := hqS
    etale_q := hqE
    kernelPair_X' := hR'
    kernelPair_Y := hTY
    isPushout_chart := hPush
    isPushout_relation := hRelPush
    aR_s := has
    aR_t := hat
    bR_s := hbs
    bR_t := hbt
    etaleRelation := hrel }, s₀, t₀, hR₀, hkRs, hgRs, hK₁, hG₁, rfl, rfl, rfl, by simp, by simp,
      by simp, by simp, by simp⟩


/-- **The compatible pair of charts of [Stacks Project, Tag 07VX], from a lifted chart.**  Let
`i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces over `S`.
Let `q : V ⟶ Y` be a surjective étale chart, `p : U ⟶ X` its base change along `f` (the cartesian
square `hpbf`, so that `g : U ⟶ V` is the projection), and `p' : U' ⟶ X'` an étale chart whose
base change along `i` is `p` (the cartesian square `hpbi`, with `k : U ⟶ U'` the projection).
Then the kernel pairs and the two pushouts of schemes they determine form a
`AlgebraicGeometry.Space.ThickeningAffineAtlas` for the span.

The étale chart `p'` is the lift of `p` across the thickening, which [Stacks Project, Tag 05ZS]
provides; it is surjective because `p` and `i` are. -/
theorem C1573.nonempty_thickeningAffineAtlas_of_isPullback
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {U U' V : BigFppfOver B S hS} (q : yoneda.obj V ⟶ Y.1) (p : yoneda.obj U ⟶ X.1)
    (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U') (g : U ⟶ V)
    (hqS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hp'E : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p')
    (hpbf : IsPullback p (yoneda.map g) f.hom q)
    (hpbi : IsPullback (yoneda.map k) p p' i.hom) :
    Nonempty (ThickeningAffineAtlas B S hS i f) := by
  obtain ⟨A, -⟩ := exists_thickeningAffineAtlas_of_isPullback B S hS hi hf q p p' k g hqS hqE
    hp'E hpbf hpbi
  exact ⟨A⟩

/-- **The pushout of [Stacks Project, Tag 07VX] exists, for a span with a lifted chart.**  A
thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` of algebraic spaces over `S` have a
pushout in the category of algebraic spaces over `S` as soon as a surjective étale chart of `Y`,
restricted to `X`, lifts to an étale chart of `X'`. -/
theorem C1573.hasPushout_of_isPullback_chart
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {U U' V : BigFppfOver B S hS} (q : yoneda.obj V ⟶ Y.1) (p : yoneda.obj U ⟶ X.1)
    (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U') (g : U ⟶ V)
    (hqS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hp'E : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p')
    (hpbf : IsPullback p (yoneda.map g) f.hom q)
    (hpbi : IsPullback (yoneda.map k) p p' i.hom) :
    HasPushout i f := by
  obtain ⟨A⟩ := nonempty_thickeningAffineAtlas_of_isPullback B S hS hi hf q p p' k g hqS hqE
    hp'E hpbf hpbi
  obtain ⟨E, a, b, h, -⟩ := isPushout_quotient_of_thickeningAffineAtlas B S hS A
  exact h.hasPushout

/-- **`Y ⟶ Y'` is a thickening, for a span with a lifted chart.**  For a thickening
`i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` of algebraic spaces over `S` such that a
surjective étale chart of `Y`, restricted to `X`, lifts to an étale chart of `X'`, the morphism
from `Y` into the pushout `Y ⨿_X X'` is a thickening. -/
theorem C1573.pushout_inr_isThickening_of_isPullback_chart
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {U U' V : BigFppfOver B S hS} (q : yoneda.obj V ⟶ Y.1) (p : yoneda.obj U ⟶ X.1)
    (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U') (g : U ⟶ V)
    (hqS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hp'E : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p')
    (hpbf : IsPullback p (yoneda.map g) f.hom q)
    (hpbi : IsPullback (yoneda.map k) p p' i.hom) [HasPushout i f] :
    IsThickeningHom B S hS (pushout.inr i f) := by
  obtain ⟨A⟩ := nonempty_thickeningAffineAtlas_of_isPullback B S hS hi hf q p p' k g hqS hqE
    hp'E hpbf hpbi
  exact pushout_inr_isThickening_of_thickeningAffineAtlas B S hS A

/-- Every thickening-and-affine span of algebraic spaces over `S` admits a compatible pair of
étale scheme charts as soon as, for every such span, some surjective étale chart of the affine
target, restricted to the source, lifts across the thickening to an étale chart.  That lift is
what [Stacks Project, Tag 05ZS] provides. -/
theorem C1573.hasThickeningAffineAtlases_of_forall_chartLift
    (hlift : ∀ {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y),
      IsThickeningHom B S hS i → IsAffineHom B S hS f.hom →
      ∃ (U U' V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1) (p : yoneda.obj U ⟶ X.1)
        (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U') (g : U ⟶ V),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) q ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) q ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) p' ∧
        IsPullback p (yoneda.map g) f.hom q ∧ IsPullback (yoneda.map k) p p' i.hom) :
    HasThickeningAffineAtlases B S hS := by
  intro X X' Y i f hi hf
  obtain ⟨U, U', V, q, p, p', k, g, hqS, hqE, hp'E, hpbf, hpbi⟩ := hlift i f hi hf
  exact nonempty_thickeningAffineAtlas_of_isPullback B S hS hi hf q p p' k g hqS hqE hp'E
    hpbf hpbi

end AlgebraicGeometry.Space

end
