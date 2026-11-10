module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.CategoryTheory.Sites.SubfunctorSheafifyPreimage

/-!
# Étale localization of a morphism of algebraic spaces at a quasi-finite point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite type and
separated, and let `x` be a point of `|X|` with image `y` in `|Y|` at which `f` is quasi-finite.
This file proves **Stacks 0ADU**: there are an étale morphism of pointed algebraic spaces
`(U, u) ⟶ (Y, y)` and a decomposition `U ×_Y X = W ⨿ V` into open-and-closed subspaces with
`V ⟶ U` finite and carrying a point `v` of `|V|` lying over `x` in `|X|` and over `u` in `|U|`.

## Main definitions

No new definitions are introduced.

## Main results

The inverse-image compatibility this file consumes,
`CategoryTheory.Subfunctor.preimage_sheafify` — sheafification of a subfunctor commutes with
inverse images along a morphism of presheaves of types — is imported from
`StacksFrontier.CategoryTheory.Sites.SubfunctorSheafifyPreimage`, which states it for values in an
independent universe.
* `CategoryTheory.Subfunctor.isIso_fromPreimage`: the comparison morphism from the inverse
  image of a subfunctor along an isomorphism to that subfunctor is an isomorphism.
* `AlgebraicGeometry.Space.mem_range_pointsMap_ι_or_of_sheafify_sup_eq_top`: a point of a
  presheaf two of whose subfunctors have join sheafifying to everything lies in the image of
  one of the two.
* `AlgebraicGeometry.Space.exists_etale_decomposition_isFinite_point_of_isQuasiFiniteAt`:
  **Stacks 0ADU**.

## Implementation notes

*The tag sits on one declaration.* Stacks 0ADU has a single assertion — its enumerated items
(1)–(3) are hypotheses — so the covering set is the one theorem stating it, and the three
auxiliary results carry no attribute.

*The quasi-compactness-or-decency hypothesis of Stacks 082H is discharged, not assumed.* Stacks
0ADU is the single-point case of Stacks 082H,
`AlgebraicGeometry.Space.exists_etale_decomposition_isFinite_of_isQuasiFiniteAt`, with the
fourth hypothesis of that lemma — that `f` be quasi-compact or its target be decent — removed.
The source removes it by first replacing `Y` by a scheme étale over it through `y`, a scheme
being decent; that last step is `AlgebraicGeometry.Space.isDecentSpace_yoneda`. So the chart
`g₀ : h_{U₀} ⟶ Y` of `AlgebraicGeometry.Space.exists_etale_chart_point_of_point` is chosen
first, Tag 03H4 (`AlgebraicGeometry.Space.exists_points_of_isPullback`) lifts `x` to a point of
`|U₀ ×_Y X|` over the chart point, and Stacks 082H is applied to `U₀ ×_Y X ⟶ h_{U₀}` there.

*The étale neighbourhood is produced as an object of the site.* The source asks only for an
étale morphism of pointed algebraic *spaces* `(U, u) ⟶ (Y, y)`; what is produced here, as in
Stacks 082H, is a representable `h_U`, which is an algebraic space by
`AlgebraicGeometry.isAlgebraicSpace_yoneda`, so the existential statement of the tag is
witnessed by something more specific than it asks for. Likewise the decomposition is stated by
the pair of subfunctors, their openness and closedness, the sheafification of their join being
everything and their meet being the sheafification of nothing — this repository's rendering of
`U ×_Y X = W ⨿ V`.

*The decomposition is transported along the comparison of the two fibre products.* What Stacks
082H returns lives on `U₁ ×_{U₀} (U₀ ×_Y X)`, while the statement asks for a decomposition of
`U₁ ×_Y X`; the two are identified by
`CategoryTheory.Limits.pullbackRightPullbackFstIso`. The two subspaces are carried across as
inverse images, which keeps openness and closedness
(`AlgebraicGeometry.Space.isOpenSubspace_preimage` and
`AlgebraicGeometry.Space.isClosedSubspace_preimage`), commutes with the sheafifications in the
decomposition clauses (`CategoryTheory.Subfunctor.preimage_sheafify`) and keeps finiteness, the
comparison morphism of the inverse images being an isomorphism.

*The point of the finite part.* Stacks 082H says only that every point of the fibre of
`|V| ⟶ |U|` over `u` lies over one of the prescribed points and that no point of the fibre of
`|W| ⟶ |U|` does. The point `v` the tag asks for is obtained by lifting `u` and the point of
`|U₀ ×_Y X|` to a point of `|U₁ ×_{U₀} (U₀ ×_Y X)|` by Tag 03H4 and observing that the second
clause forbids it from lying in `W`.

*The `HasSheafify` assumption of Stacks 082H is discharged here.* That lemma carries
`CategoryTheory.HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)` as a
standing assumption on the ambient site; it is a theorem of this library,
`AlgebraicGeometry.BigFppfOver.hasSheafify_type`, so the statement below carries exactly the
three hypotheses of the tag and no assumption about the site.

## References

* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Subfunctor

/-- **Sheafification of a subfunctor commutes with inverse images.** The sieve cut out of a
section of the source by the inverse image of `G` is the sieve cut out of its image by `G`, so
the two sheafifications have the same sections. -/
theorem preimage_sheafify {C : Type*} [Category C] (J : GrothendieckTopology C)
    {F F' : Cᵒᵖ ⥤ Type u} (G : Subfunctor F) (p : F' ⟶ F) :
    (G.preimage p).sheafify J = (G.sheafify J).preimage p := by
  have hsieve {T : Cᵒᵖ} (s : F'.obj T) :
      (G.preimage p).sieveOfSection s = G.sieveOfSection (p.app T s) := by
    ext Z i
    change p.app _ (F'.map i.op s) ∈ G.obj _ ↔ F.map i.op (p.app T s) ∈ G.obj _
    rw [NatTrans.naturality_apply]
  ext T s
  change (G.preimage p).sieveOfSection s ∈ J T.unop ↔
    G.sieveOfSection (p.app T s) ∈ J T.unop
  rw [hsieve]

/-- **The inverse image of a subfunctor along an isomorphism is isomorphic to it.** The
comparison morphism `CategoryTheory.Subfunctor.fromPreimage` is inverted by the morphism
carrying a section of the subfunctor to its image under the inverse isomorphism, which lies in
the inverse image because the two isomorphisms compose to the identity. -/
instance isIso_fromPreimage {C : Type*} [Category C] {F F' : Cᵒᵖ ⥤ Type u}
    (G : Subfunctor F) (p : F' ⟶ F) [IsIso p] : IsIso (G.fromPreimage p) := by
  have hcomp : (G.ι ≫ inv p) ≫ p = G.ι := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hle : range (G.ι ≫ inv p) ≤ G.preimage p := by
    rw [← image_top, image_le_iff, ← preimage_comp, hcomp, top_le_iff, preimage_eq_top_iff,
      range_ι]
  refine ⟨lift (G.ι ≫ inv p) hle, (cancel_mono (G.preimage p).ι).1 ?_,
    (cancel_mono G.ι).1 ?_⟩
  · simp [fromPreimage_ι_assoc]
  · simp [fromPreimage_ι]

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site needs the larger budget
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
instance hasPullbacks_presheaf_EtaleSplitQuasiFinitePoint :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_EtaleSplitQuasiFinitePoint
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A point of a presheaf covered by two subfunctors lies in the image of one of them.** If
the join of `W` and `V` sheafifies to everything then the coproduct of the two inclusions is
locally surjective, hence surjective on the points of Tag 03BU. -/
theorem mem_range_pointsMap_ι_or_of_sheafify_sup_eq_top
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W V : Subfunctor F)
    (hsup : (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (z : points B S hS F) :
    z ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∨
      z ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  classical
  have hb (b : ULift.{u} Bool) :
      cond b.down V W ≤
        Subfunctor.range (Sigma.desc fun b : ULift.{u} Bool ↦ (cond b.down V W).ι) :=
    calc cond b.down V W = Subfunctor.range (cond b.down V W).ι := (Subfunctor.range_ι _).symm
      _ = Subfunctor.range (Sigma.ι (fun b : ULift.{u} Bool ↦ (cond b.down V W).toFunctor) b ≫
            Sigma.desc fun b ↦ (cond b.down V W).ι) := by simp
      _ ≤ _ := Subfunctor.range_comp_le _ _
  have hle : W ⊔ V ≤
      Subfunctor.range (Sigma.desc fun b : ULift.{u} Bool ↦ (cond b.down V W).ι) :=
    sup_le (hb ⟨false⟩) (hb ⟨true⟩)
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun b : ULift.{u} Bool ↦ (cond b.down V W).ι) := by
    rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
    refine top_le_iff.1 ?_
    rw [← hsup]
    exact Subfunctor.sheafify_le_sheafify _ hle
  have hcover := points_cover_of_isLocallySurjective_sigma_desc B S hS F (ULift.{u} Bool)
    (fun b ↦ cond b.down V W) hls
  have hz : z ∈ ⋃ b : ULift.{u} Bool,
      Set.range (pointsMap B S hS (cond b.down V W).toFunctor (cond b.down V W).ι) := by
    rw [hcover]
    exact Set.mem_univ z
  obtain ⟨⟨b⟩, hb⟩ := Set.mem_iUnion.mp hz
  cases b
  · exact Or.inl hb
  · exact Or.inr hb

/-- **Stacks Project, Tag 0ADU.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`,
let `x` be a point of `|X|` and let `y` be its image in `|Y|`. Assume that `f` is locally of
finite type, that `f` is separated and that `f` is quasi-finite at `x`. Then there are an object
`U` of the big fppf category over `S`, an **étale** morphism `g : h_U ⟶ Y` and a point `u` of
`|h_U|` over `y`, together with a decomposition of `U ×_Y X` into two open-and-closed subspaces
`W` and `V` — their join sheafifies to everything and their meet is the sheafification of
nothing — such that `V ⟶ U` is **finite** and some point of `|V|` lies over `x` in `|X|` and
over `u` in `|U|`.

This is the single-point case of Stacks 082H,
`AlgebraicGeometry.Space.exists_etale_decomposition_isFinite_of_isQuasiFiniteAt`, applied over
an étale scheme chart of `Y` through `y`; see the module documentation for how the extra
hypothesis of that lemma and its standing `HasSheafify` assumption on the site are both
discharged. The hypotheses are those of the tag and nothing else. -/
@[stacks 0ADU]
theorem exists_etale_decomposition_isFinite_point_of_isQuasiFiniteAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) (y : points B S hS Y)
    (hxy : pointsMap B S hS X f x = y)
    (hft : IsLocallyOfFiniteType B S hS f) (hsep : IsSeparated B S hS f)
    (hqf : IsQuasiFiniteAt B S hS f x) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y)
      (u : points B S hS (yoneda.obj U)) (W V : Subfunctor (pullback g f)),
      IsEtale B S hS g ∧
      pointsMap B S hS (yoneda.obj U) g u = y ∧
      IsOpenSubspace B S hS W ∧ IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS V ∧ IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor (pullback g f)).sheafify (BigFppfOver.topology B S hS) ∧
      IsFinite B S hS (V.ι ≫ pullback.fst g f) ∧
      ∃ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.snd g f) v = x ∧
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst g f) v = u := by
  classical
  have hsheafify : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    BigFppfOver.hasSheafify_type B S hS
  -- an étale scheme chart of `Y` through `y`
  obtain ⟨U₀, g₀, u₀, hg₀E, hg₀u⟩ := exists_etale_chart_point_of_point B S hS Y hY y
  have hU₀ : IsAlgebraicSpace B S hS (yoneda.obj U₀) := isAlgebraicSpace_yoneda B S hS U₀
  have hP₀ : IsAlgebraicSpace B S hS (pullback g₀ f) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS g₀ f hU₀ hX hY
  -- a point of `|U₀ ×_Y X|` over the chart point and over `x`
  obtain ⟨x', hx'u, hx'x⟩ :=
    exists_points_of_isPullback B S hS (IsPullback.of_hasPullback g₀ f) u₀ x
      (by rw [hg₀u, hxy])
  -- Stacks 082H for the base change over the chart, at the single point `x'`
  obtain ⟨U₁, g₁, u₁, W, V, hg₁E, hg₁u, hWo, hWc, hVo, hVc, hsup, hinf, hVfin, -, hWpt⟩ :=
    exists_etale_decomposition_isFinite_of_isQuasiFiniteAt B S hS hP₀ hU₀
      (pullback.fst g₀ f) u₀ (fun _ : Fin 1 ↦ x') (fun _ ↦ hx'u)
      (isLocallyOfFiniteType_pullback_fst B S hS hX hY hft U₀ g₀)
      (isSeparated_pullbackFst B S hS g₀ hsep)
      (fun _ ↦ (isQuasiFiniteAt_iff_of_isPullback B S hS (IsPullback.of_hasPullback g₀ f)
        hX hY hU₀ hft x').2 (by rw [hx'x]; exact hqf))
      (Or.inr (isDecentSpace_yoneda B S hS U₀))
  have hU₁ : IsAlgebraicSpace B S hS (yoneda.obj U₁) := isAlgebraicSpace_yoneda B S hS U₁
  have hQ : IsAlgebraicSpace B S hS (pullback g₁ (pullback.fst g₀ f)) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS g₁ (pullback.fst g₀ f)
      hU₁ hP₀ hU₀
  have hR : IsAlgebraicSpace B S hS (pullback (g₁ ≫ g₀) f) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS (g₁ ≫ g₀) f hU₁ hX hY
  -- the comparison of `U₁ ×_{U₀} (U₀ ×_Y X)` with `U₁ ×_Y X`
  obtain ⟨e, hefst, hesnd⟩ :
      ∃ e : pullback g₁ (pullback.fst g₀ f) ≅ pullback (g₁ ≫ g₀) f,
        e.inv ≫ pullback.fst g₁ (pullback.fst g₀ f) = pullback.fst (g₁ ≫ g₀) f ∧
          e.inv ≫ pullback.snd g₁ (pullback.fst g₀ f) ≫ pullback.snd g₀ f =
            pullback.snd (g₁ ≫ g₀) f :=
    ⟨pullbackRightPullbackFstIso g₀ f g₁, pullbackRightPullbackFstIso_inv_fst g₀ f g₁,
      pullbackRightPullbackFstIso_inv_snd_snd g₀ f g₁⟩
  -- a point of `|U₁ ×_{U₀} (U₀ ×_Y X)|` over `u₁` and `x'`, which must lie in `V`
  obtain ⟨z, hzu, hzx⟩ :=
    exists_points_of_isPullback B S hS (IsPullback.of_hasPullback g₁ (pullback.fst g₀ f)) u₁ x'
      (by rw [hg₁u, hx'u])
  obtain ⟨v₀, hv₀⟩ : ∃ v, pointsMap B S hS V.toFunctor V.ι v = z := by
    rcases mem_range_pointsMap_ι_or_of_sheafify_sup_eq_top B S hS W V hsup z with
      ⟨t, ht⟩ | ⟨v, hv⟩
    · exact absurd (by rw [pointsMap_comp_apply, ht, hzx])
        (hWpt t (by rw [pointsMap_comp_apply, ht, hzu]) 0)
    · exact ⟨v, hv⟩
  have hvv : pointsMap B S hS (V.preimage e.inv).toFunctor (V.fromPreimage e.inv)
      (pointsMap B S hS V.toFunctor (inv (V.fromPreimage e.inv)) v₀) = v₀ := by
    rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id_eq]
  refine ⟨U₁, g₁ ≫ g₀, u₁, W.preimage e.inv, V.preimage e.inv,
    isEtale_comp B S hS hg₁E hg₀E, by rw [pointsMap_comp_apply, hg₁u, hg₀u],
    isOpenSubspace_preimage B S hS e.inv W hQ hR hWo,
    isClosedSubspace_preimage B S hS e.inv W hQ hR hWc,
    isOpenSubspace_preimage B S hS e.inv V hQ hR hVo,
    isClosedSubspace_preimage B S hS e.inv V hQ hR hVc, ?_, ?_, ?_, ?_⟩
  · have hpre : W.preimage e.inv ⊔ V.preimage e.inv = (W ⊔ V).preimage e.inv := rfl
    have htop : (⊤ : Subfunctor (pullback g₁ (pullback.fst g₀ f))).preimage e.inv = ⊤ := rfl
    rw [hpre, Subfunctor.preimage_sheafify, hsup, htop]
  · have hpre : W.preimage e.inv ⊓ V.preimage e.inv = (W ⊓ V).preimage e.inv := rfl
    have hbot : (⊥ : Subfunctor (pullback g₁ (pullback.fst g₀ f))).preimage e.inv = ⊥ := rfl
    rw [hpre, hinf, ← Subfunctor.preimage_sheafify, hbot]
  · have hcomm : V.fromPreimage e.inv ≫ V.ι ≫ pullback.fst g₁ (pullback.fst g₀ f) =
        ((V.preimage e.inv).ι ≫ pullback.fst (g₁ ≫ g₀) f) ≫ 𝟙 (yoneda.obj U₁) := by
      rw [Category.comp_id, Subfunctor.fromPreimage_ι_assoc, hefst]
    exact isFinite_of_isPullback B S hS (IsPullback.of_horiz_isIso ⟨hcomm⟩) hVfin
  · refine ⟨pointsMap B S hS V.toFunctor (inv (V.fromPreimage e.inv)) v₀, ?_, ?_⟩
    · have hmorph : (V.preimage e.inv).ι ≫ pullback.snd (g₁ ≫ g₀) f =
          V.fromPreimage e.inv ≫ V.ι ≫ pullback.snd g₁ (pullback.fst g₀ f) ≫
            pullback.snd g₀ f := by
        rw [Subfunctor.fromPreimage_ι_assoc, ← hesnd]
      rw [hmorph, pointsMap_comp_apply, hvv, pointsMap_comp_apply, hv₀, pointsMap_comp_apply,
        hzx, hx'x]
    · have hmorph : (V.preimage e.inv).ι ≫ pullback.fst (g₁ ≫ g₀) f =
          V.fromPreimage e.inv ≫ V.ι ≫ pullback.fst g₁ (pullback.fst g₀ f) := by
        rw [Subfunctor.fromPreimage_ι_assoc, ← hefst]
      rw [hmorph, pointsMap_comp_apply, hvv, pointsMap_comp_apply, hv₀, hzu]

end AlgebraicGeometry.Space

end
