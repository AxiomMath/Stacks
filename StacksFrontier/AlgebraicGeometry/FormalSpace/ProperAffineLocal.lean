module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperEtaleLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringOfOpenCover
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# Properness of a morphism of formal algebraic spaces from its affine base changes

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of fppf sheaves
over `S` whose base change along every point of `Y` out of an *affine* object of the site is an
algebraic space over `S` proper over that affine is proper in the sense of **Stacks 0AM6**.

This is the implication (3) ⇒ (1) of **Stacks 0ART**, and it is where **Stacks 02WQ** in the
value universe of a formal algebraic space is used.

## Main results

* `AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_pullback_sigma_affineOpens`: the base
  change of `f` along the coproduct of the affine opens of a point of `Y` is an algebraic space
  over `S`.
* `AlgebraicGeometry.FormalSpace.isProper_of_affine_base_changes`: the criterion.

## Implementation notes

An arbitrary point `ξ : T ⟶ Y` is covered by the coproduct `V` of the affine opens of `T`,
which lies in the site because the index type and the members are all bounded by `size T`
(`AlgebraicGeometry.BigFppfOver.exists_surjective_etale_sigma_of_openCover`). The base change of
`f` along `V ⟶ T ⟶ Y` decomposes as the coproduct of its base changes along the affine opens,
coproducts of sheaves of sets being van Kampen
(`CategoryTheory.Sheaf.isColimitCofanMkPullback`), and each of those is an algebraic space over
`S` by hypothesis. Stacks 02WQ in the value universe `Type (u + 1)`
(`AlgebraicGeometry.Space.isAlgebraicSpaceULift_coproduct_of_size_le`) then makes the whole base
change an algebraic space, the atlases it needs being the affine ones of
`AlgebraicGeometry.Space.exists_affine_atlas_size_le_of_isProperULift`, whose sizes are bounded
by `size T` because each member is proper over an affine open of `T`. That is the only use of
properness in this step, and it is what the *uniform* size bound needs.

Representability by algebraic spaces then follows because it is étale local on the target
(`AlgebraicGeometry.FormalSpace.isRepresentable_of_forall_surjective_etale_cover`), and
properness follows from it along the fppf covering family of the affine opens of the point
(`AlgebraicGeometry.FormalSpace.isProper_of_isRepresentable_of_forall_fppfFamily`, the family
form of Stacks 0422). The family form is what avoids a second coproduct: properness of
`∐ᵢ Wᵢ ⟶ ∐ᵢ Uᵢ` is never needed.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 0ART](https://stacks.math.columbia.edu/tag/0ART)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine opens of an object of the big fppf site of `S`, as a family of objects of the
site covering it by open immersions, together with the bound on the index type and on the
members by the size of the object. -/
private theorem exists_affineOpens_cover_site (T : BigFppfOver B S hS) :
    ∃ (I : Type u) (X : I → BigFppfOver B S hS) (g : ∀ i, X i ⟶ T),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (X i))) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj T,
        ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      #I ≤ ((BigFppfOver.toScheme B S hS).obj T).size ∧
      ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤
        ((BigFppfOver.toScheme B S hS).obj T).size := by
  classical
  set W : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj T
  let hU (i : W.affineOpens) : B.Contains (i.1 : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι T.left.property
  let fO (i : W.affineOpens) : B.obj (hU i) ⟶ T.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hU i)) ⟶ B.inclusion.obj T.left from i.1.ι)
  let X (i : W.affineOpens) : BigFppfOver B S hS := Over.mk (fO i ≫ T.hom)
  let g (i : W.affineOpens) : X i ⟶ T := Over.homMk (fO i) (by simp [X])
  have hfmap (i : W.affineOpens) : (BigFppfOver.toScheme B S hS).map (g i) = i.1.ι :=
    B.inclusion.map_preimage _
  refine ⟨W.affineOpens, X, g, fun i => i.2, fun i => ?_, fun x => ?_,
    Scheme.mk_affineOpens_le_size W, fun i => Scheme.size_coe_opens_le W i.1⟩
  · rw [hfmap i]
    infer_instance
  · obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
    refine ⟨i, ⟨x, hxi⟩, ?_⟩
    rw [hfmap i]
    rfl

/-- Transport of the algebraic-space condition along an isomorphism `F ≅ G`, together with
properness of the precomposition of a proper morphism out of `G`. -/
private theorem isAlgebraicSpaceULift_and_isProperULift_precomp
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ G) (f : G ⟶ K)
    (hG : Space.IsAlgebraicSpaceULift.{u + 1} B S hS G)
    (hK : Space.IsAlgebraicSpaceULift.{u + 1} B S hS K)
    (hf : Space.IsProperULift.{u + 1} B S hS f) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS F ∧
      Space.IsProperULift.{u + 1} B S hS (e.hom ≫ f) :=
  have hF := Space.isAlgebraicSpaceULift_of_iso B S hS e.symm hG
  ⟨hF, Space.isProperULift_precomp B S hS e f hF hG hK hf⟩

/-- **The base change of `f` along the coproduct of the affine opens of a scheme-valued point
of its target is an algebraic space over `S`**, as soon as its base change along every point out
of an affine object of the site is an algebraic space over `S` proper over that affine.

The coproduct of the affine opens of the point lies in the site, the base change over it is the
coproduct of the base changes over the affine opens by van Kampen, and Stacks 02WQ in the value
universe `Type (u + 1)` applies: the affine atlases of the members have sizes bounded uniformly
by that of the point, properness over an affine being what bounds them. -/
theorem isAlgebraicSpaceULift_pullback_sigma_affineOpens {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (halg : ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ g : (uliftYoneda.{u + 1}).obj Z ⟶ Y.obj,
        Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback g f.hom) ∧
        Space.IsProperULift.{u + 1} B S hS (pullback.fst g f.hom))
    (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ Y.obj) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ T),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS
        (pullback ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom) := by
  classical
  let J := BigFppfOver.topology B S hS
  obtain ⟨I, Xf, gX, haff, hopen, hcovT, hIsize, hXsize⟩ :=
    exists_affineOpens_cover_site B S hS T
  obtain ⟨V, j, q, hjq, hqsurj, hqet, -, ⟨hcofanV⟩⟩ :=
    BigFppfOver.exists_surjective_etale_sigma_of_openCover B S hS Xf T gX hopen hcovT
      T.left.property hIsize hXsize
  -- the sheaf-level point and the sheaf-level base change
  set ξs : J.uliftYoneda.{u + 1}.obj T ⟶ Y := ⟨ξ⟩
  set ζ : J.uliftYoneda.{u + 1}.obj V ⟶ Y := J.uliftYoneda.{u + 1}.map q ≫ ξs with hζ
  set fam : ∀ i, J.uliftYoneda.{u + 1}.obj (Xf i) ⟶ Y :=
    fun i => J.uliftYoneda.{u + 1}.map (gX i) ≫ ξs
  have hApb : IsPullback (pullback.fst ζ f) (pullback.snd ζ f) ζ f :=
    IsPullback.of_hasPullback ζ f
  have hAcofan := Sheaf.isColimitCofanMkPullback J
    (fun i => J.uliftYoneda.{u + 1}.map (j i)) hcofanV (pullback.fst ζ f)
  -- the base change over `V` decomposes as the coproduct of the base changes over the
  -- affine opens
  have hpaste (i : I) : IsPullback
      (pullback.snd (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ f) ≫
        pullback.snd ζ f)
      (pullback.fst (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ f)) f (fam i) := by
    have hcomp : J.uliftYoneda.{u + 1}.map (j i) ≫ ζ = fam i := by
      rw [hζ, ← Category.assoc, ← Functor.map_comp, hjq i]
    exact hcomp ▸ ((IsPullback.of_hasPullback
      (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ f)).flip.paste_horiz hApb.flip)
  -- each summand is an algebraic space with an affine atlas of size at most that of the point
  have key : ∀ i, ∃ (Ti : BigFppfOver B S hS)
      (ai : (uliftYoneda.{u + 1}).obj Ti ⟶
        (pullback (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ f)).obj),
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS
        (pullback (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ f)).obj ∧
      (Space.surjectiveOnSite B S hS).relative (uliftYoneda.{u + 1}) ai ∧
      (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) ai ∧
      ((BigFppfOver.toScheme B S hS).obj Ti).size ≤
        ((BigFppfOver.toScheme B S hS).obj T).size := by
    intro i
    obtain ⟨halgi, hpropi⟩ := halg (Xf i) (haff i) (fam i).hom
    let e : (pullback (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ f)).obj ≅
        pullback (fam i).hom f.hom :=
      ((hpaste i).flip.map (sheafToPresheaf J (Type (u + 1)))).isoPullback
    obtain ⟨hAi, hp⟩ := isAlgebraicSpaceULift_and_isProperULift_precomp B S hS e _ halgi
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (Xf i)) hpropi
    obtain ⟨Ti, ai, -, hs, het, hsz⟩ :=
      Space.exists_affine_atlas_size_le_of_isProperULift B S hS (haff i) hAi _ hp
    exact ⟨Ti, ai, hAi, hs, het, hsz.trans (hXsize i)⟩
  choose Ti ai hAi hs het hsz using key
  -- Stacks 02WQ in the value universe of a formal algebraic space
  have hGalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ζ f).obj :=
    Space.isAlgebraicSpaceULift_coproduct_of_size_le B S hS hAi
      (fun i => pullback.snd (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ f))
      hAcofan Ti ai hs het
      (Scheme.aleph0_le_size ((BigFppfOver.toScheme B S hS).obj T)) T.left.property
      hIsize hsz
  exact ⟨V, q, hqsurj, hqet, Space.isAlgebraicSpaceULift_of_iso B S hS
    (hApb.map (sheafToPresheaf J (Type (u + 1)))).isoPullback hGalg⟩

/-- **Stacks 0ART, (3) implies (1).** A morphism of formal algebraic spaces over `S` whose base
change along every point of its target out of an affine object of the site is an algebraic space
over `S` proper over that affine is proper.

Representability by algebraic spaces is read off
`AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_pullback_sigma_affineOpens` by locality on
the target, and properness then descends along the family of affine opens of each point, which
is an fppf covering family of it by **Stacks 0DFC**. -/
theorem isProper_of_affine_base_changes {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (halg : ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ g : (uliftYoneda.{u + 1}).obj Z ⟶ Y.obj,
        Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback g f.hom) ∧
        Space.IsProperULift.{u + 1} B S hS (pullback.fst g f.hom)) :
    IsProper B S hS f := by
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
    isRepresentable_of_forall_surjective_etale_cover B S hS f
      (isAlgebraicSpaceULift_pullback_sigma_affineOpens B S hS f halg)
  refine isProper_of_isRepresentable_of_forall_fppfFamily B S hS f hrep fun U ξ => ?_
  obtain ⟨I, Xf, gX, haff, hopen, hcovU, -, -⟩ := exists_affineOpens_cover_site B S hS U
  refine ⟨ULift.{u + 1} I, fun i => Xf i.down, fun i => gX i.down, ?_,
    fun i => (halg (Xf i.down) (haff i.down) _).2⟩
  exact Space.IsFppfCovering.reindex B S hS
    (Space.isFppfCovering_yoneda_of_openCover B S hS Xf gX hopen hcovU)
    (σ := fun i : ULift.{u + 1} I => i.down) fun i => ⟨ULift.up i, rfl⟩

/-- **Stacks 0ART, (3) implies (1).** A morphism of formal algebraic spaces over `S` all of
whose base changes along affine schemes over `S` in the site are proper is proper.

Condition (3) gives, at an affine point `Z ⟶ Y`, properness of the chosen base change as a
morphism of formal algebraic spaces; read at the identity point of `Z`
(**Stacks 0ART, (3) implies (4)**) that is exactly the hypothesis of
`AlgebraicGeometry.FormalSpace.isProper_of_affine_base_changes`, namely that the base change is
an algebraic space over `S` proper over `Z`. -/
@[stacks 0ART "(3) implies (1)"]
theorem IsProperOnAffineBaseChanges.isProper {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsProperOnAffineBaseChanges B S hS f) : IsProper B S hS f := by
  refine isProper_of_affine_base_changes B S hS f fun Z hZ g => ?_
  set gs : schemeSheaf B S hS Z ⟶ Y := ObjectProperty.homMk g
  obtain ⟨hW, hp⟩ := h.isAlgebraicAndProper B S hS Z hZ gs _ (pullback.fst gs f)
    (pullback.snd gs f) (IsPullback.of_hasPullback gs f)
  have hpre : IsPullback ((pullback.fst gs f).hom) ((pullback.snd gs f).hom) g f.hom :=
    (IsPullback.of_hasPullback gs f).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  obtain ⟨halgpre, hp'⟩ := isAlgebraicSpaceULift_and_isProperULift_precomp B S hS
    hpre.isoPullback.symm _ hW (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Z) hp
  exact ⟨halgpre, by simpa [hpre.isoPullback_inv_fst] using hp'⟩

/-- **Stacks 0ART, (1) is equivalent to (3).** A morphism of formal algebraic spaces over `S`
is proper exactly when each of its base changes along an affine scheme over `S` in the site is
proper. -/
@[stacks 0ART "(1) is equivalent to (3)"]
theorem isProper_iff_isProperOnAffineBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsProper B S hS f ↔ IsProperOnAffineBaseChanges B S hS f :=
  ⟨fun hf => (hf.isProperOnSchemeBaseChanges B S hS).isProperOnAffineBaseChanges B S hS,
    IsProperOnAffineBaseChanges.isProper B S hS⟩

end AlgebraicGeometry.FormalSpace

end
