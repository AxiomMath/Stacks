module

public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange.ComparisonMap
import all StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange.ComparisonMap

/-!
# Stacks 03FN, part (6): the base-changed relation is the kernel pair of the comparison map

The kernel pair of the map from two copies of the chart to the glued scheme, computed as four
blocks, and its identification with the base-changed relation, first in schemes and then in the
slice category over the base.

This is part of `StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange`, whose module
docstring describes the whole argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

variable [FiniteDimensional k K] [IsGalois k K]

/-! ### The kernel pair of the comparison map of part (6) -/

/-- **Pullback distributes over a binary coproduct, with the two squares given as data.** This
is `AlgebraicGeometry.TwistedDoubledOrigin.coproductPullback_isPullback` with the two chosen
fibre products replaced by arbitrary Cartesian squares over the same morphism, transported
along the two comparison isomorphisms. -/
private theorem isPullback_coprod_desc {T W X₀ X₁ P₀ P₁ : Scheme.{u}} (f₀ : X₀ ⟶ T)
    (f₁ : X₁ ⟶ T) (e : W ⟶ T)
    {a₀ : P₀ ⟶ X₀} {b₀ : P₀ ⟶ W} {a₁ : P₁ ⟶ X₁} {b₁ : P₁ ⟶ W}
    (h₀ : IsPullback a₀ b₀ f₀ e) (h₁ : IsPullback a₁ b₁ f₁ e) :
    IsPullback (coprod.desc (a₀ ≫ coprod.inl) (a₁ ≫ coprod.inr)) (coprod.desc b₀ b₁)
      (coprod.desc f₀ f₁) e := by
  have hdist := coproductPullback_isPullback (fun b : Bool => bif b then X₀ else X₁)
    (Bool.rec (motive := fun b : Bool => (bif b then X₀ else X₁) ⟶ T) f₁ f₀) e
  refine hdist.of_iso (coprod.mapIso h₀.isoPullback.symm h₁.isoPullback.symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  · apply coprod.hom_ext <;> simp <;> rfl
  · apply coprod.hom_ext <;> simp

omit [FiniteDimensional k K] [IsGalois k K] in
/-- **The kernel pair of the comparison map of part (6).** The fibre product of the map from
two copies of the chart to the glued scheme with itself is `(U ⨿ V) ⨿ (V ⨿ U)`, where `V` is
the gluing locus — the puncture — of the gluing datum.

The four summands are the four blocks of the kernel pair, indexed by the pair of chart labels:
on the two diagonal blocks the two charts coincide and the block is `U` itself, both charts
being open immersions, hence monomorphisms
(`CategoryTheory.IsKernelPair.id_of_mono`); on the two off-diagonal blocks the two charts meet
exactly in the gluing locus, which is
`Stacks.Examples.doubleSectionCover_isPullback_chart`. The grouping is by the *first* chart
label: the first group is the pair of blocks whose first coordinate lies in the first copy of
the chart, the second group the pair whose first coordinate lies in the second copy. -/
theorem isPullback_doubledChartsToGlued :
    IsPullback
      (coprod.desc (coprod.desc coprod.inl ((puncturedCover K).ι ≫ coprod.inl))
        (coprod.desc ((puncturedCover K).ι ≫ coprod.inr) coprod.inr))
      (coprod.desc (coprod.desc coprod.inl ((puncturedCover K).ι ≫ coprod.inr))
        (coprod.desc ((puncturedCover K).ι ≫ coprod.inl) coprod.inr))
      (doubledChartsToGlued k K) (doubledChartsToGlued k K) := by
  -- the two diagonal blocks and the two off-diagonal blocks
  have hdiag : ∀ b : Bool, IsPullback (𝟙 (cover K)) (𝟙 (cover K))
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart b)
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart b) := fun b =>
    have := (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).isOpenImmersion_chart
      b
    IsKernelPair.id_of_mono _
  have htf := Stacks.Examples.doubleSectionCover_isPullback_chart (cover K) (puncturedCover K)
    (show (true : Bool) ≠ false by decide)
  have hft := Stacks.Examples.doubleSectionCover_isPullback_chart (cover K) (puncturedCover K)
    (show (false : Bool) ≠ true by decide)
  -- the two groups, each a distributivity over the coproduct of the two charts
  have hcol₀ : IsPullback (coprod.desc (𝟙 (cover K)) (puncturedCover K).ι)
      (coprod.desc coprod.inl ((puncturedCover K).ι ≫ coprod.inr))
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart true)
      (doubledChartsToGlued k K) := by
    have h := (isPullback_coprod_desc
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart true)
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart false)
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart true)
      (hdiag true) hft).flip
    rwa [Category.id_comp] at h
  have hcol₁ : IsPullback (coprod.desc (puncturedCover K).ι (𝟙 (cover K)))
      (coprod.desc ((puncturedCover K).ι ≫ coprod.inl) coprod.inr)
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart false)
      (doubledChartsToGlued k K) := by
    have h := (isPullback_coprod_desc
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart true)
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart false)
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart false)
      htf (hdiag false)).flip
    rwa [Category.id_comp] at h
  have hkey := isPullback_coprod_desc
    ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart true)
    ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart false)
    (doubledChartsToGlued k K) hcol₀ hcol₁
  rwa [coprod.desc_comp, coprod.desc_comp, Category.id_comp, Category.id_comp] at hkey

/-! ### The base-changed relation is the kernel pair of the comparison map -/

/-- The permutation of a four-fold coproduct regrouping the summands `(A ⨿ D) ⨿ (B ⨿ C)` as
`(A ⨿ B) ⨿ (C ⨿ D)`. -/
private def coprodShuffle (A B C D : Scheme.{u}) : (A ⨿ D) ⨿ (B ⨿ C) ≅ (A ⨿ B) ⨿ (C ⨿ D) where
  hom := coprod.desc (coprod.desc (coprod.inl ≫ coprod.inl) (coprod.inr ≫ coprod.inr))
    (coprod.desc (coprod.inr ≫ coprod.inl) (coprod.inl ≫ coprod.inr))
  inv := coprod.desc (coprod.desc (coprod.inl ≫ coprod.inl) (coprod.inl ≫ coprod.inr))
    (coprod.desc (coprod.inr ≫ coprod.inr) (coprod.inr ≫ coprod.inl))
  hom_inv_id := by
    apply coprod.hom_ext <;> apply coprod.hom_ext <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Category.comp_id]
  inv_hom_id := by
    apply coprod.hom_ext <;> apply coprod.hom_ext <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Category.comp_id]

/-- **The extra chart factor times the relation scheme, split into four pieces.** Pulling the
relation scheme back along the chart map gives `(U ⨿ V) ⨿ (V ⨿ U)`, where `V` is the puncture:
over the diagonal summand of the relation the fibre product is the self-product of the chart,
which is two copies of the chart (`coverFiberProductSplitIso`), and over the punctured summand
it is two copies of the puncture (`isPullback_puncturedSelfProduct`).

The four summands are listed in the order matching the four blocks of
`isPullback_doubledChartsToGlued`, which is *not* the order in which the two applications of
distributivity produce them — the latter groups by relation summand, the former by the chart
label of the first coordinate — so the two are matched by the four-fold coproduct permutation
`coprodShuffle`. On the third summand the two parametrisations of the puncture differ by the
Galois automorphism, which is why the second summand of the punctured block is reparametrised
by `galoisActionPuncturedMap` before the permutation. -/
private theorem isPullback_coverPullbackRelation (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    IsPullback
      (coprod.desc (coprod.desc (𝟙 (cover K)) (puncturedCover K).ι)
        (coprod.desc (puncturedCover K).ι (𝟙 (cover K))))
      (coprod.desc (coprod.desc coprod.inl coprod.inr)
        (coprod.desc (galoisActionPuncturedMap k K σ ≫ coprod.inr)
          (galoisAction k K σ ≫ coprod.inl)))
      (coverMap k K) (relationOverBase k K).hom := by
  have hinv : galoisAction k K σ ≫ galoisAction k K σ = 𝟙 (cover K) :=
    galoisAction_involutive k K hdegree σ
  -- the diagonal summand of the relation: the self-product of the chart
  have hsplit : IsPullback (coprod.desc (𝟙 (cover K)) (𝟙 (cover K)))
      (coprod.desc (𝟙 (cover K)) (galoisAction k K σ)) (coverMap k K) (coverMap k K) :=
    IsPullback.of_iso_pullback ⟨by apply coprod.hom_ext <;> simp [galoisAction_coverMap]⟩
      (coverFiberProductSplitIso k K hdegree σ hσ).symm
      (coverFiberProductSplitIso_inv_fst k K hdegree σ hσ)
      (coverFiberProductSplitIso_second_factor k K hdegree σ hσ)
  -- the punctured summand, reparametrised so that both copies of the puncture include by `ι`
  have hpunct : IsPullback
      (coprod.desc (𝟙 (puncturedCover K).toScheme) (galoisActionPuncturedMap k K σ))
      (coprod.desc (puncturedCover K).ι (puncturedCover K).ι)
      ((puncturedCover K).ι ≫ coverMap k K) (coverMap k K) := by
    have hτ : galoisActionPuncturedMap k K σ ≫ (puncturedCover K).ι ≫ galoisAction k K σ =
        (puncturedCover K).ι := by
      rw [← Category.assoc, galoisActionPuncturedMap_ι, Category.assoc, hinv, Category.comp_id]
    refine (isPullback_puncturedSelfProduct k K hdegree σ hσ).flip.of_iso'
      (coprod.mapIso (Iso.refl (puncturedCover K).toScheme)
        (asIso (galoisActionPuncturedMap k K σ)))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · apply coprod.hom_ext <;> simp
    · apply coprod.hom_ext <;> simp [hτ]
  -- distributivity over the two summands of the relation scheme
  have hdist := (isPullback_coprod_desc (coverMap k K)
    ((puncturedCover K).ι ≫ coverMap k K) (coverMap k K) hsplit.flip hpunct).flip
  simp only [coprod.desc_comp, Category.id_comp] at hdist
  -- regroup the four summands
  refine hdist.of_iso' (coprodShuffle (cover K) (puncturedCover K).toScheme
    (puncturedCover K).toScheme (cover K)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, coprodShuffle, Iso.refl_hom, Category.comp_id]
    apply coprod.hom_ext <;> apply coprod.hom_ext <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc]
  · simp only [Iso.symm_hom, coprodShuffle, Iso.refl_hom, Category.comp_id]
    apply coprod.hom_ext <;> apply coprod.hom_ext <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc]

/-- The first projection absorbs a product map with the identity on the left factor, read on
underlying schemes. -/
private theorem prodMap_id_left_comp_fst {A B B' : Over (base k)} (φ : B ⟶ B') :
    (prod.map (𝟙 A) φ).left ≫ (prod.fst (X := A) (Y := B')).left =
      (prod.fst (X := A) (Y := B)).left := by
  rw [← Over.comp_left, prod.map_fst, Category.comp_id]

/-- The second projection turns a product map with the identity on the left factor into the
right component, read on underlying schemes. -/
private theorem prodMap_id_left_comp_snd {A B B' : Over (base k)} (φ : B ⟶ B') :
    (prod.map (𝟙 A) φ).left ≫ (prod.snd (X := A) (Y := B')).left =
      (prod.snd (X := A) (Y := B)).left ≫ φ.left := by
  rw [← Over.comp_left, prod.map_snd, Over.comp_left]

/-- **The splitting of the extra chart factor times the relation scheme**, as an isomorphism
with the four-summand scheme carrying the kernel pair of the comparison map of part (6). -/
private def coverRelationSplitIso (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    (cover K ⨿ (puncturedCover K).toScheme) ⨿ ((puncturedCover K).toScheme ⨿ cover K) ≅
      (coverOverBase k K ⨯ relationOverBase k K).left :=
  (isPullback_coverPullbackRelation k K hdegree σ hσ).isoPullback ≪≫
    (Over.prodLeftIsoPullback (coverOverBase k K) (relationOverBase k K)).symm

@[reassoc]
private theorem coverRelationSplitIso_hom_fst (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coverRelationSplitIso k K hdegree σ hσ).hom ≫
        (prod.fst (X := coverOverBase k K) (Y := relationOverBase k K)).left =
      coprod.desc (coprod.desc (𝟙 (cover K)) (puncturedCover K).ι)
        (coprod.desc (puncturedCover K).ι (𝟙 (cover K))) := by
  rw [coverRelationSplitIso, Iso.trans_hom, Category.assoc, Iso.symm_hom,
    Over.prodLeftIsoPullback_inv_fst]
  exact IsPullback.isoPullback_hom_fst _

@[reassoc]
private theorem coverRelationSplitIso_hom_snd (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coverRelationSplitIso k K hdegree σ hσ).hom ≫
        (prod.snd (X := coverOverBase k K) (Y := relationOverBase k K)).left =
      coprod.desc (coprod.desc coprod.inl coprod.inr)
        (coprod.desc (galoisActionPuncturedMap k K σ ≫ coprod.inr)
          (galoisAction k K σ ≫ coprod.inl)) := by
  rw [coverRelationSplitIso, Iso.trans_hom, Category.assoc, Iso.symm_hom,
    Over.prodLeftIsoPullback_inv_snd]
  exact IsPullback.isoPullback_hom_snd _

/-- The first projection of the self-product of the chart, read backwards through the
splitting. -/
private theorem coverSelfProductIso_inv_fst (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coverSelfProductIso k K hdegree σ hσ).inv ≫
        (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)).left =
      coprod.desc (𝟙 (cover K)) (𝟙 (cover K)) := by
  rw [coverSelfProductIso, Iso.trans_inv, Category.assoc,
    Over.prodLeftIsoPullback_inv_fst]
  exact coverFiberProductSplitIso_inv_fst k K hdegree σ hσ

/-- The second projection of the self-product of the chart, read backwards through the
splitting. -/
private theorem coverSelfProductIso_inv_snd (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coverSelfProductIso k K hdegree σ hσ).inv ≫
        (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)).left =
      coprod.desc (𝟙 (cover K)) (galoisAction k K σ) := by
  rw [coverSelfProductIso, Iso.trans_inv, Category.assoc,
    Over.prodLeftIsoPullback_inv_snd]
  exact coverFiberProductSplitIso_second_factor k K hdegree σ hσ

/-- **The base-changed relation is the kernel pair of the comparison map of part (6).** The
two legs of `doubledRelation` exhibit `U ×_S R` as the fibre product of
`doubledSelfProductToGlued` with itself.

The comparison map factors as the splitting isomorphism of the self-product followed by
`doubledChartsToGlued`, whose kernel pair is computed by
`isPullback_doubledChartsToGlued`; `isPullback_comp_iso_self` moves that computation across the
isomorphism, and `coverRelationSplitIso` identifies the resulting four-summand corner with
`U ×_S R`. The two identifications of the legs are checked on the two projections of the
self-product, where the splitting isomorphism becomes the two descriptions
`coverSelfProductIso_inv_fst` and `coverSelfProductIso_inv_snd`. -/
theorem isPullback_doubledRelation_left (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    IsPullback (doubledRelation k K σ).target.left (doubledRelation k K σ).source.left
      (doubledSelfProductToGlued k K hdegree σ hσ).left
      (doubledSelfProductToGlued k K hdegree σ hσ).left := by
  have hinv : galoisAction k K σ ≫ galoisAction k K σ = 𝟙 (cover K) :=
    galoisAction_involutive k K hdegree σ
  have hiotaσ : galoisActionPuncturedMap k K σ ≫ (puncturedCover K).ι =
      (puncturedCover K).ι ≫ galoisAction k K σ := galoisActionPuncturedMap_ι k K σ
  have hiotaσ' : galoisActionPuncturedMap k K σ ≫ (puncturedCover K).ι ≫
      galoisAction k K σ = (puncturedCover K).ι := by
    rw [← Category.assoc, hiotaσ, Category.assoc, hinv, Category.comp_id]
  have hrf : (relationFirst k K).left = coprod.desc (𝟙 (cover K)) (puncturedCover K).ι := rfl
  have hrs : (relationSecond k K σ).left =
      coprod.desc (𝟙 (cover K)) ((puncturedCover K).ι ≫ galoisAction k K σ) := rfl
  -- the two legs of the base-changed relation, read through the splittings
  have htgt : (coverRelationSplitIso k K hdegree σ hσ).hom ≫
      (doubledRelation k K σ).target.left =
      (coprod.desc (coprod.desc coprod.inl ((puncturedCover K).ι ≫ coprod.inl))
        (coprod.desc ((puncturedCover K).ι ≫ coprod.inr) coprod.inr)) ≫
        (coverSelfProductIso k K hdegree σ hσ).inv := by
    rw [doubledRelation_target]
    apply prodLeft_hom_ext
    · simp only [Category.assoc]
      rw [prodMap_id_left_comp_fst, coverRelationSplitIso_hom_fst,
        coverSelfProductIso_inv_fst]
      apply coprod.hom_ext <;> apply coprod.hom_ext <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Category.comp_id]
    · simp only [Category.assoc]
      rw [prodMap_id_left_comp_snd, coverRelationSplitIso_hom_snd_assoc,
        coverSelfProductIso_inv_snd, hrf]
      apply coprod.hom_ext <;> apply coprod.hom_ext <;>
        simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
          coprod.inr_desc_assoc, Category.comp_id, hiotaσ]
  have hsrc : (coverRelationSplitIso k K hdegree σ hσ).hom ≫
      (doubledRelation k K σ).source.left =
      (coprod.desc (coprod.desc coprod.inl ((puncturedCover K).ι ≫ coprod.inr))
        (coprod.desc ((puncturedCover K).ι ≫ coprod.inl) coprod.inr)) ≫
        (coverSelfProductIso k K hdegree σ hσ).inv := by
    rw [doubledRelation_source]
    apply prodLeft_hom_ext
    · simp only [Category.assoc]
      rw [prodMap_id_left_comp_fst, coverRelationSplitIso_hom_fst,
        coverSelfProductIso_inv_fst]
      apply coprod.hom_ext <;> apply coprod.hom_ext <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Category.comp_id]
    · simp only [Category.assoc]
      rw [prodMap_id_left_comp_snd, coverRelationSplitIso_hom_snd_assoc,
        coverSelfProductIso_inv_snd, hrs]
      apply coprod.hom_ext <;> apply coprod.hom_ext <;>
        simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
          coprod.inr_desc_assoc, Category.comp_id, hiotaσ']
  -- transport the kernel pair of the untwisted comparison map
  refine isPullback_comp_iso_self _ _ (coverSelfProductIso k K hdegree σ hσ)
    (doubledChartsToGlued k K) ?_
  refine (isPullback_doubledChartsToGlued k K).of_iso'
    (coverRelationSplitIso k K hdegree σ hσ).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rw [Iso.inv_comp_eq, ← Category.assoc, htgt, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rw [Iso.inv_comp_eq, ← Category.assoc, hsrc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

/-! ### The kernel pair, read in the slice category over the base -/

/-- The underlying morphism of schemes of the comparison map of part (6). -/
theorem doubledSelfProductToGlued_left (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    (doubledSelfProductToGlued k K hdegree σ hσ).left =
      (coverSelfProductIso k K hdegree σ hσ).hom ≫ doubledChartsToGlued k K := rfl

/-- **The base-changed relation is the kernel pair of the comparison map of part (6), in the
slice category over the base.** The forgetful functor from the slice category creates connected
limits, and a fibre square is a connected limit, so a Cartesian square of underlying schemes
whose data lies over the base is Cartesian over the base. -/
theorem isPullback_doubledRelation (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    IsPullback (doubledRelation k K σ).target (doubledRelation k K σ).source
      (doubledSelfProductToGlued k K hdegree σ hσ)
      (doubledSelfProductToGlued k K hdegree σ hσ) :=
  IsPullback.of_map_of_faithful (Over.forget (base k))
    (isPullback_doubledRelation_left k K hdegree σ hσ)

/-- **The relation covers the kernel pair of the comparison map exactly.** The comparison map
from the base-changed relation to the fibre square of `doubledSelfProductToGlued` with itself is
an isomorphism, being the comparison isomorphism of two fibre squares over the same cospan. -/
theorem isIso_pullbackLift_doubledRelation (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    IsIso (pullback.lift (doubledRelation k K σ).target (doubledRelation k K σ).source
      (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ)) := by
  have h := isPullback_doubledRelation k K hdegree σ hσ
  have hlift : pullback.lift (doubledRelation k K σ).target (doubledRelation k K σ).source
      (doubledRelation_comp_doubledSelfProductToGlued k K hdegree σ hσ) =
      h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  rw [hlift]
  infer_instance

end AlgebraicGeometry.TwistedDoubledOrigin

end
