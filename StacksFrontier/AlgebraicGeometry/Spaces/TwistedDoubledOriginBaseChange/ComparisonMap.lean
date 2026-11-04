module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongCoproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperComplementExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginEtaleOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginAwayFromZero
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginEtaleRelation
public import StacksFrontier.Examples.GroupSchemes.DoubleGlue

/-!
# Stacks 03FN, part (6): the comparison map and its invariance under the base-changed relation

The chart `U ⟶ S` as a scheme over the base, the glued scheme of part (6) and the map from two
copies of the chart to it (an fppf covering), the base change `doubledRelation` of the twisted
relation along `U ⟶ S`, and the proof that the comparison map `doubledSelfProductToGlued`
coequalises its two legs.

This is part of `StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange`, whose module
docstring describes the whole argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The chart, as a scheme over the base via its own structure morphism. -/
def uToBase : coverOverBase k K ⟶ baseOverBase k :=
  Over.homMk (coverMap k K) (by simp [coverOverBase, baseOverBase])

/-- The glued scheme of part (6) — two copies of the chart glued along the puncture — as a
scheme over the base, via the projection to the chart followed by the chart's structure
morphism. -/
abbrev doubledOverBase : Over (base k) :=
  Over.mk ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).proj ≫
    coverMap k K)

/-- Two copies of the chart, as the charts of the gluing datum defining the glued scheme of
part (6). -/
abbrev doubledChartsScheme (k K : Type u) [Field k] [Field K] [Algebra k K] : Scheme.{u} :=
  cover K ⨿ cover K

/-- The map from two copies of the chart to the glued scheme, sending each copy to its
corresponding chart of the gluing datum.

The two chart morphisms are taken from `Stacks.Examples.doubleSectionCover` rather than
rebuilding them from `Stacks.Examples.doubleGlueData.ι`: the latter's stated domain is the
gluing datum's `U`-valued index function, only definitionally (through unfolding
`CategoryTheory.GlueData.ofGlueData'`) equal to `cover K`, and the `SectionCoverData` field
already carries the identification made once, at its own definition. -/
def doubledChartsToGlued :
    doubledChartsScheme k K ⟶
      (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).total :=
  coprod.desc
    ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart true)
    ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart false)

/-- Each chart of the gluing datum is a section of the projection to the chart, so the
comparison map is a section of the projection on both summands. -/
theorem doubledChartsToGlued_comp_proj :
    doubledChartsToGlued k K ≫
        (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).proj =
      coprod.desc (𝟙 (cover K)) (𝟙 (cover K)) := by
  simp only [doubledChartsToGlued, coprod.desc_comp,
    (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart_comp_proj]

/-- The two copies of the chart, as a scheme over the base via the two structure morphisms
combined. -/
abbrev doubledChartsOverBase : Over (base k) :=
  Over.mk (coprod.desc (coverMap k K) (coverMap k K) : doubledChartsScheme k K ⟶ base k)

/-- The comparison map from two copies of the chart to the glued scheme of part (6), as a
morphism over the base. -/
def doubledChartsToGluedOverBase :
    doubledChartsOverBase k K ⟶ doubledOverBase k K :=
  Over.homMk (doubledChartsToGlued k K) (by
    change doubledChartsToGlued k K ≫
        ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).proj ≫
          coverMap k K) =
      coprod.desc (coverMap k K) (coverMap k K)
    rw [← Category.assoc, doubledChartsToGlued_comp_proj]
    apply coprod.hom_ext <;> simp)

/-- The two charts of the gluing datum cover the glued scheme: this is
`Stacks.Examples.SectionCoverData.exists_chart_eq`, unwound to a union of ranges. -/
theorem range_doubledChartsToGlued_eq_univ :
    Set.range ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart true) ∪
      Set.range
        ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart false) =
      Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨b, y, hy⟩ :=
    (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).exists_chart_eq x
  cases b
  · exact Set.mem_union_right _ ⟨y, hy⟩
  · exact Set.mem_union_left _ ⟨y, hy⟩

/-- **The comparison map of part (6) is an fppf covering.** Each chart of the gluing datum is
an open immersion, hence flat and locally of finite presentation, and the two charts are
jointly surjective since they cover the glued scheme. -/
theorem doubledChartsToGlued_fppf :
    Flat (doubledChartsToGlued k K) ∧ LocallyOfFinitePresentation (doubledChartsToGlued k K) ∧
      Surjective (doubledChartsToGlued k K) := by
  have h1 : IsOpenImmersion
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart true) :=
    (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).isOpenImmersion_chart true
  have h2 : IsOpenImmersion
      ((Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart false) :=
    (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).isOpenImmersion_chart
      false
  refine ⟨flat_coprodDesc _ _, locallyOfFinitePresentation_coprodDesc _ _,
    surjective_coprodDesc _ _ (range_doubledChartsToGlued_eq_univ K)⟩

/-! ### The comparison map of part (6) is invariant under the base-changed relation -/

/-- The Galois automorphism of the chart, as an automorphism of the chart over the base. -/
def galoisActionOver (σ : K ≃ₐ[k] K) : coverOverBase k K ⟶ coverOverBase k K :=
  Over.homMk (galoisAction k K σ) (galoisAction_coverMap k K σ)

/-- The underlying morphism of schemes of `galoisActionOver` is `galoisAction`. -/
@[simp]
theorem galoisActionOver_left (σ : K ≃ₐ[k] K) :
    (galoisActionOver k K σ).left = galoisAction k K σ := rfl

/-- The inclusion of the diagonal summand of the relation scheme, over the base. -/
def relationInl : coverOverBase k K ⟶ relationOverBase k K :=
  Over.homMk coprod.inl (coprod.inl_desc _ _)

/-- The inclusion of the punctured twisted summand of the relation scheme, over the base. -/
def relationInr : coverPuncturedOverBase k K ⟶ relationOverBase k K :=
  Over.homMk coprod.inr (coprod.inr_desc _ _)

/-- The underlying morphism of schemes of `relationInl` is the left coproduct inclusion. -/
@[simp]
theorem relationInl_left : (relationInl k K).left = coprod.inl := rfl

/-- The underlying morphism of schemes of `relationInr` is the right coproduct inclusion. -/
@[simp]
theorem relationInr_left : (relationInr k K).left = coprod.inr := rfl

/-- The first leg of the relation restricts to the identity on the diagonal summand. -/
@[simp]
theorem relationInl_relationFirst : relationInl k K ≫ relationFirst k K = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp

/-- The second leg of the relation restricts to the identity on the diagonal summand. -/
@[simp]
theorem relationInl_relationSecond (σ : K ≃ₐ[k] K) :
    relationInl k K ≫ relationSecond k K σ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp

/-- The first leg of the relation restricts to the inclusion `coverPuncturedInclusion` on the
punctured twisted summand. -/
@[simp]
theorem relationInr_relationFirst :
    relationInr k K ≫ relationFirst k K = coverPuncturedInclusion k K := by
  apply Over.OverMorphism.ext
  simp [coverPuncturedInclusion]

/-- The second leg of the relation restricts, on the punctured twisted summand, to the inclusion
`coverPuncturedInclusion` followed by the Galois automorphism `galoisActionOver`. -/
@[simp]
theorem relationInr_relationSecond (σ : K ≃ₐ[k] K) :
    relationInr k K ≫ relationSecond k K σ =
      coverPuncturedInclusion k K ≫ galoisActionOver k K σ := by
  apply Over.OverMorphism.ext
  simp [coverPuncturedInclusion, galoisActionOver]

/-- Two morphisms out of a binary product in the slice over the base agree as soon as their
composites with the two projections do, read in schemes: the product is the fibre product over
the base, whose two projections are jointly monic. -/
private theorem prodLeft_hom_ext {A B : Over (base k)} {W : Scheme.{u}}
    {x y : W ⟶ (A ⨯ B).left}
    (hfst : x ≫ (prod.fst (X := A) (Y := B)).left =
      y ≫ (prod.fst (X := A) (Y := B)).left)
    (hsnd : x ≫ (prod.snd (X := A) (Y := B)).left =
      y ≫ (prod.snd (X := A) (Y := B)).left) :
    x = y := by
  rw [← cancel_mono (Over.prodLeftIsoPullback A B).hom]
  apply pullback.hom_ext
  · simpa only [Category.assoc, Over.prodLeftIsoPullback_hom_fst] using hfst
  · simpa only [Category.assoc, Over.prodLeftIsoPullback_hom_snd] using hsnd

variable [FiniteDimensional k K] [IsGalois k K]

/-- The first summand of `U ⨿ U`, read through the splitting of the self-product, has the
identity as its first projection. -/
private theorem inl_comp_coverFiberProductSplitIso_inv_fst (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coprod.inl : cover K ⟶ cover K ⨿ cover K) ≫
        (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫
          pullback.fst (coverMap k K) (coverMap k K) = 𝟙 (cover K) := by
  rw [← Category.assoc, coverFiberProductSplitIso_inl, pullback.diagonal_fst]

/-- Read through the splitting of the self-product of the chart, the first projection of its
structure map agrees with the structure map of the two copies of the chart of part (6). -/
theorem coverFiberProductSplitIso_inv_fst_comp (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.fst (coverMap k K) (coverMap k K) ≫ coverMap k K =
      coprod.desc (coverMap k K) (coverMap k K) := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc]
    simpa using congrArg (· ≫ coverMap k K)
      (inl_comp_coverFiberProductSplitIso_inv_fst k K hdegree σ hσ)
  · rw [coprod.inr_desc]
    simpa using congrArg (· ≫ coverMap k K) (coverFiberProductSplitIso_inr_fst k K hdegree σ hσ)

/-- The same identification, stated through the splitting isomorphism in the other
direction. -/
theorem coverFiberProductSplitIso_hom_comp (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    (coverFiberProductSplitIso k K hdegree σ hσ).hom ≫
        coprod.desc (coverMap k K) (coverMap k K) =
      pullback.fst (coverMap k K) (coverMap k K) ≫ coverMap k K := by
  have h := congrArg (fun f => (coverFiberProductSplitIso k K hdegree σ hσ).hom ≫ f)
    (coverFiberProductSplitIso_inv_fst_comp k K hdegree σ hσ)
  simpa [← Category.assoc, Iso.hom_inv_id] using h.symm

/-- **The self-product of the chart over the base, identified with the two copies of the
chart of part (6), as schemes over the base.** Under `coverSelfProductIso`, the structure map
of the self-product (its first projection followed by the chart map) agrees with the structure
map of two copies of the chart combined, so the isomorphism of underlying schemes upgrades to
an isomorphism over the base. -/
def coverSelfProductOverIso (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coverOverBase k K ⨯ coverOverBase k K) ≅ doubledChartsOverBase k K :=
  Over.isoMk (coverSelfProductIso k K hdegree σ hσ) (by
    change (coverSelfProductIso k K hdegree σ hσ).hom ≫
        (coprod.desc (coverMap k K) (coverMap k K) : doubledChartsScheme k K ⟶ base k) =
      (coverOverBase k K ⨯ coverOverBase k K).hom
    have hfst : ((coverOverBase k K).prodLeftIsoPullback (coverOverBase k K)).hom ≫
        pullback.fst (coverMap k K) (coverMap k K) =
        (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)).left :=
      Over.prodLeftIsoPullback_hom_fst (coverOverBase k K) (coverOverBase k K)
    rw [coverSelfProductIso, Iso.trans_hom, Category.assoc, coverFiberProductSplitIso_hom_comp,
      ← Category.assoc, hfst]
    exact Over.w (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)))

/-- Reading a product with a fixed factor `Z'` on the left through `Over.prodLeftIsoPullback`
on both sides turns it into `pullback.map`: this is the naturality square needed to transport
the twisted relation's gluing identity across the extra `Z'` factor introduced by base change. -/
private lemma prodMap_id_left_comp_prodLeftIsoPullback {R' W' : Over (base k)} (φ : R' ⟶ W')
    (Z' : Over (base k)) :
    (prod.map (𝟙 Z') φ).left ≫ (Over.prodLeftIsoPullback Z' W').hom =
      (Over.prodLeftIsoPullback Z' R').hom ≫
        pullback.map Z'.hom R'.hom Z'.hom W'.hom (𝟙 Z'.left) φ.left (𝟙 (base k))
          (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left, prod.map_fst, Category.comp_id,
      pullback.lift_fst, Category.comp_id, Over.prodLeftIsoPullback_hom_fst]
  · simp only [Category.assoc]
    rw [Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left, prod.map_snd, pullback.lift_snd,
      Over.comp_left, ← Over.prodLeftIsoPullback_hom_snd, Category.assoc]

/-- **Pullback distributes over the coproduct decomposition of the relation scheme.** Pulling
back the chart map `coverMap k K` against the structure map of `relationOverBase k K` (itself a
binary coproduct of two maps to the base) agrees with the coproduct of the two pullbacks against
the summands. This is the scheme-level input needed to transport part (6)'s relation across the
extra chart factor introduced by base change; it rests on the existing Mathlib fact that pulling
back a map out of a coproduct distributes over the coproduct in an extensive category (here,
`Scheme`), via `AlgebraicGeometry.isPullback_sigmaDesc_sigmaMap`, bridged from the binary
coproduct `relationScheme K` to the two-element indexed family through
`AlgebraicGeometry.coprodIsoSigma`. -/
private def relationPullbackCoprodIso :
    (∐ fun i : ULift.{u} WalkingPair ↦
      pullback (coverMap k K) (coprodDescFamily (coverMap k K)
        ((puncturedCover K).ι ≫ coverMap k K) i)) ≅
      pullback (coverMap k K) (relationOverBase k K).hom := by
  refine (isPullback_sigmaDesc_sigmaMap
    (coprodDescFamily (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K))
    (coverOverBase k K)).isoPullback ≪≫ pullback.congrHom rfl
      (coprodIsoSigma_inv_comp_coprodDesc (coverMap k K)
        ((puncturedCover K).ι ≫ coverMap k K)).symm ≪≫
    asIso (pullback.map (coverMap k K)
      ((coprodIsoSigma (cover K) (puncturedCover K).toScheme).inv ≫
        coprod.desc (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K))
      (coverMap k K) (relationOverBase k K).hom (𝟙 (cover K))
      (coprodIsoSigma (cover K) (puncturedCover K).toScheme).inv (𝟙 (base k))
      (by simp) (by simp))

/-- The first summand's inclusion into `U ×_S R`, read through `relationPullbackCoprodIso` as
the component of the comparison isomorphism indexed by `⟨WalkingPair.left⟩`. -/
private def relationPullbackInl :
    pullback (coverMap k K) (coverMap k K) ⟶ pullback (coverMap k K) (relationOverBase k K).hom :=
  pullback.map (coverMap k K) (coverMap k K) (coverMap k K) (relationOverBase k K).hom
    (𝟙 (cover K)) coprod.inl (𝟙 (base k)) (by simp)
    (by simp [relationOverBase, coprod.inl_desc])

/-- The second summand's inclusion into `U ×_S R`, read through `relationPullbackCoprodIso` as
the component of the comparison isomorphism indexed by `⟨WalkingPair.right⟩`. -/
private def relationPullbackInr :
    pullback (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K) ⟶
      pullback (coverMap k K) (relationOverBase k K).hom :=
  pullback.map (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K) (coverMap k K)
    (relationOverBase k K).hom (𝟙 (cover K)) coprod.inr (𝟙 (base k)) (by simp)
    (by simp [relationOverBase, coprod.inr_desc])

omit [FiniteDimensional k K] [IsGalois k K] in
/-- The `⟨WalkingPair.left⟩` component of `relationPullbackCoprodIso` is
`relationPullbackInl`. -/
private theorem sigmaι_left_comp_relationPullbackCoprodIso_hom :
    Sigma.ι (fun i : ULift.{u} WalkingPair ↦
        pullback (coverMap k K) (coprodDescFamily (coverMap k K)
          ((puncturedCover K).ι ≫ coverMap k K) i)) ⟨WalkingPair.left⟩ ≫
      (relationPullbackCoprodIso k K).hom = relationPullbackInl k K := by
  apply pullback.hom_ext
  · simp [Category.assoc, relationPullbackCoprodIso, Iso.trans_hom, asIso_hom,
      pullback.congrHom_hom, relationPullbackInl, pullback.lift_fst, Category.comp_id,
      IsPullback.isoPullback_hom_fst]
  · simp [Category.assoc, relationPullbackCoprodIso, Iso.trans_hom, asIso_hom,
      pullback.congrHom_hom, relationPullbackInl, pullback.lift_snd, pullback.lift_snd_assoc,
      ι_left_coprodIsoSigma_inv]

omit [FiniteDimensional k K] [IsGalois k K] in
/-- The `⟨WalkingPair.right⟩` component of `relationPullbackCoprodIso` is
`relationPullbackInr`. -/
private theorem sigmaι_right_comp_relationPullbackCoprodIso_hom :
    Sigma.ι (fun i : ULift.{u} WalkingPair ↦
        pullback (coverMap k K) (coprodDescFamily (coverMap k K)
          ((puncturedCover K).ι ≫ coverMap k K) i)) ⟨WalkingPair.right⟩ ≫
      (relationPullbackCoprodIso k K).hom = relationPullbackInr k K := by
  apply pullback.hom_ext
  · simp [Category.assoc, relationPullbackCoprodIso, Iso.trans_hom, asIso_hom,
      pullback.congrHom_hom, relationPullbackInr, pullback.lift_fst, Category.comp_id,
      IsPullback.isoPullback_hom_fst]
  · simp [Category.assoc, relationPullbackCoprodIso, Iso.trans_hom, asIso_hom,
      pullback.congrHom_hom, relationPullbackInr, pullback.lift_snd, pullback.lift_snd_assoc,
      ι_right_coprodIsoSigma_inv]

omit [FiniteDimensional k K] [IsGalois k K] in
/-- **Jointly-epic pair recognising `U ×_S R`.** Two morphisms out of `U ×_S R` agree as soon
as they agree after precomposing with `relationPullbackInl` and `relationPullbackInr`: these
are, up to the isomorphism `relationPullbackCoprodIso`, the two inclusions of a binary
coproduct into itself. -/
private theorem pullback_relationOverBase_hom_ext {T : Scheme.{u}}
    {u v : pullback (coverMap k K) (relationOverBase k K).hom ⟶ T}
    (hl : relationPullbackInl k K ≫ u = relationPullbackInl k K ≫ v)
    (hr : relationPullbackInr k K ≫ u = relationPullbackInr k K ≫ v) : u = v := by
  rw [← cancel_epi (relationPullbackCoprodIso k K).hom]
  apply Sigma.hom_ext
  rintro ⟨_ | _⟩
  · rwa [← Category.assoc, ← Category.assoc, sigmaι_left_comp_relationPullbackCoprodIso_hom]
  · rwa [← Category.assoc, ← Category.assoc, sigmaι_right_comp_relationPullbackCoprodIso_hom]

/-- **The pre-relation on `U ×_S U` induced by base-changing the twisted relation along
`U ⟶ S`.** Its source object is `U` times the relation scheme of part (6)'s relation, its
target `U ×_S U` is the self-product of the chart, and its two legs are the base change of
`relationFirst`/`relationSecond` by the identity on the extra `U` factor. -/
def doubledRelation (σ : K ≃ₐ[k] K) :
    Stacks.Groupoids.PreRelation (coverOverBase k K ⨯ relationOverBase k K)
      (coverOverBase k K ⨯ coverOverBase k K) :=
  prod.lift (prod.map (𝟙 (coverOverBase k K)) (relationFirst k K))
    (prod.map (𝟙 (coverOverBase k K)) (relationSecond k K σ))

omit [FiniteDimensional k K] [IsGalois k K] in
/-- The target leg of `doubledRelation` is the product of the identity with `relationFirst`. -/
@[simp]
theorem doubledRelation_target (σ : K ≃ₐ[k] K) :
    (doubledRelation k K σ).target = prod.map (𝟙 (coverOverBase k K)) (relationFirst k K) := by
  simp [doubledRelation, Stacks.Groupoids.PreRelation.target]

omit [FiniteDimensional k K] [IsGalois k K] in
/-- The source leg of `doubledRelation` is the product of the identity with `relationSecond`. -/
@[simp]
theorem doubledRelation_source (σ : K ≃ₐ[k] K) :
    (doubledRelation k K σ).source =
      prod.map (𝟙 (coverOverBase k K)) (relationSecond k K σ) := by
  simp [doubledRelation, Stacks.Groupoids.PreRelation.source]

/-- **The map from the self-product of the chart to the glued scheme of part (6), as a
morphism over the base.** This is `f''` of the base-change argument: the comparison
isomorphism `coverSelfProductOverIso` to the two-chart scheme, followed by the comparison map
`doubledChartsToGluedOverBase` to the glued scheme. -/
def doubledSelfProductToGlued (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coverOverBase k K ⨯ coverOverBase k K) ⟶ doubledOverBase k K :=
  (coverSelfProductOverIso k K hdegree σ hσ).hom ≫ doubledChartsToGluedOverBase k K

/-- **Transporting a kernel-pair fact along a post-composed isomorphism.** If `kiso : U ≅ U'`
and `g : U' ⟶ M`, a kernel-pair fact for `g` with legs `t ≫ kiso.hom`/`s ≫ kiso.hom` landing in
`U'` transfers to one for `kiso.hom ≫ g` with the un-transported legs `t`/`s` landing in `U`.
This is the tool used to move the kernel-pair computation of `doubledSelfProductToGlued`, whose
underlying scheme map factors as `(coverSelfProductIso ...).hom ≫ doubledChartsToGlued k K`,
across to the untwisted map `doubledChartsToGlued k K` alone. -/
private theorem isPullback_comp_iso_self {R U U' M : Scheme.{u}} (t s : R ⟶ U) (kiso : U ≅ U')
    (g : U' ⟶ M) (H : IsPullback (t ≫ kiso.hom) (s ≫ kiso.hom) g g) :
    IsPullback t s (kiso.hom ≫ g) (kiso.hom ≫ g) :=
  H.of_iso' (Iso.refl R) kiso kiso (Iso.refl M) (by simp) (by simp) (by simp) (by simp)

/-- The first projection of the self-product of the chart, read through the splitting: it is
the identity on both summands, the diagonal and the twisted diagonal both having the first
coordinate as their parameter. -/
theorem coverFiberProductSplitIso_inv_fst (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.fst (coverMap k K) (coverMap k K) =
      coprod.desc (𝟙 (cover K)) (𝟙 (cover K)) := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc, inl_comp_coverFiberProductSplitIso_inv_fst]
  · rw [coverFiberProductSplitIso_inr_fst, coprod.inr_desc]

/-- **The self-product of the chart, restricted to the puncture in the second coordinate.**
`U ×_S (U ∖ {0})` is two copies of the puncture: a point of it is a point `v` of the puncture
together with a point of `U` lying over the same point of `S`, and the latter is either `v`
itself or its Galois twist. On the first copy the two coordinates are `(v, v)`, on the second
`(σ(v), v)`; the second coordinate is the parameter on both, which is why both components of
the vertical map are the identity.

This is the second summand of the base-changed relation of part (6): under
`relationPullbackCoprodIso` the extra chart factor times the relation scheme splits into the
self-product of the chart and this restricted self-product, and this lemma splits the latter in
turn. It is obtained by pasting the splitting of the self-product
(`coverFiberProductSplitIso`) against the distributivity of pullback over the binary coproduct
of the identity and the Galois automorphism, which is where the two copies come from. -/
theorem isPullback_puncturedSelfProduct (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    IsPullback
      (coprod.desc (puncturedCover K).ι ((puncturedCover K).ι ≫ galoisAction k K σ))
      (coprod.desc (𝟙 (puncturedCover K).toScheme) (𝟙 (puncturedCover K).toScheme))
      (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K) := by
  have hinv : galoisAction k K σ ≫ galoisAction k K σ = 𝟙 (cover K) :=
    galoisAction_involutive k K hdegree σ
  -- the two summands of the restricted self-product, as base changes of `𝟙` and of `σ`
  have hdiag : pullback.fst (𝟙 (cover K)) (puncturedCover K).ι =
      pullback.snd (𝟙 (cover K)) (puncturedCover K).ι ≫ (puncturedCover K).ι := by
    simpa using pullback.condition (f := 𝟙 (cover K)) (g := (puncturedCover K).ι)
  have htwist : pullback.fst (galoisAction k K σ) (puncturedCover K).ι =
      pullback.snd (galoisAction k K σ) (puncturedCover K).ι ≫
        (puncturedCover K).ι ≫ galoisAction k K σ := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, hinv, Category.comp_id]
  have hfstiso : IsIso (pullback.snd (𝟙 (cover K)) (puncturedCover K).ι) :=
    (IsPullback.of_hasPullback (𝟙 (cover K)) (puncturedCover K).ι).isIso_snd_of_isIso
  have hsndiso : IsIso (pullback.snd (galoisAction k K σ) (puncturedCover K).ι) :=
    (IsPullback.of_hasPullback (galoisAction k K σ) (puncturedCover K).ι).isIso_snd_of_isIso
  -- distributivity of pullback over the coproduct of `𝟙` and `σ`
  have hdist : IsPullback
      (coprod.desc (pullback.fst (𝟙 (cover K)) (puncturedCover K).ι ≫ coprod.inl)
        (pullback.fst (galoisAction k K σ) (puncturedCover K).ι ≫ coprod.inr))
      (coprod.desc (pullback.snd (𝟙 (cover K)) (puncturedCover K).ι)
        (pullback.snd (galoisAction k K σ) (puncturedCover K).ι))
      (coprod.desc (𝟙 (cover K)) (galoisAction k K σ)) (puncturedCover K).ι :=
    coproductPullback_isPullback (fun _ : Bool => cover K)
      (fun b => match b with
        | true => 𝟙 (cover K)
        | false => galoisAction k K σ) (puncturedCover K).ι
  have hsplit : IsPullback
      (coprod.map (puncturedCover K).ι ((puncturedCover K).ι ≫ galoisAction k K σ))
      (coprod.desc (𝟙 (puncturedCover K).toScheme) (𝟙 (puncturedCover K).toScheme))
      (coprod.desc (𝟙 (cover K)) (galoisAction k K σ)) (puncturedCover K).ι := by
    refine hdist.of_iso
      (coprod.mapIso (asIso (pullback.snd (𝟙 (cover K)) (puncturedCover K).ι))
        (asIso (pullback.snd (galoisAction k K σ) (puncturedCover K).ι)))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · apply coprod.hom_ext
      · simp [hdiag, coprod.inl_desc]
      · simp [htwist, coprod.inr_desc]
    · apply coprod.hom_ext
      · simp
      · simp
  -- transport the vertical leg to the second projection of the self-product
  have hsplit' : IsPullback
      (coprod.map (puncturedCover K).ι ((puncturedCover K).ι ≫ galoisAction k K σ) ≫
        (coverFiberProductSplitIso k K hdegree σ hσ).inv)
      (coprod.desc (𝟙 (puncturedCover K).toScheme) (𝟙 (puncturedCover K).toScheme))
      (pullback.snd (coverMap k K) (coverMap k K)) (puncturedCover K).ι := by
    refine hsplit.of_iso (Iso.refl _) (coverFiberProductSplitIso k K hdegree σ hσ).symm
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
    simpa using (coverFiberProductSplitIso_second_factor k K hdegree σ hσ).symm
  have hpaste := hsplit'.paste_horiz (IsPullback.of_hasPullback (coverMap k K) (coverMap k K))
  rwa [Category.assoc, coverFiberProductSplitIso_inv_fst k K hdegree σ hσ,
    show coprod.map (puncturedCover K).ι ((puncturedCover K).ι ≫ galoisAction k K σ) ≫
        coprod.desc (𝟙 (cover K)) (𝟙 (cover K)) =
      coprod.desc (puncturedCover K).ι ((puncturedCover K).ι ≫ galoisAction k K σ) from by
      apply coprod.hom_ext <;> simp] at hpaste

omit [FiniteDimensional k K] [IsGalois k K] in
/-- **Jointly epic pair recognising the extra chart factor times the relation scheme.** Two
morphisms out of `U ×_S R` agree as soon as they agree on the two summands of the relation
scheme: this is `pullback_relationOverBase_hom_ext`, read through the identification of the
binary product in the slice over the base with the fibre product. -/
private theorem prodMap_relation_hom_ext {T : Over (base k)}
    {u v : coverOverBase k K ⨯ relationOverBase k K ⟶ T}
    (hl : prod.map (𝟙 (coverOverBase k K)) (relationInl k K) ≫ u =
      prod.map (𝟙 (coverOverBase k K)) (relationInl k K) ≫ v)
    (hr : prod.map (𝟙 (coverOverBase k K)) (relationInr k K) ≫ u =
      prod.map (𝟙 (coverOverBase k K)) (relationInr k K) ≫ v) :
    u = v := by
  have key : ∀ {A : Over (base k)} (ι : A ⟶ relationOverBase k K)
      (w : coverOverBase k K ⨯ relationOverBase k K ⟶ T),
      pullback.map (coverOverBase k K).hom A.hom (coverOverBase k K).hom
          (relationOverBase k K).hom (𝟙 (coverOverBase k K).left) ι.left (𝟙 (base k))
          (by simp) (by simp [← Over.w ι]) ≫
        (Over.prodLeftIsoPullback (coverOverBase k K) (relationOverBase k K)).inv ≫ w.left =
      (Over.prodLeftIsoPullback (coverOverBase k K) A).inv ≫
        (prod.map (𝟙 (coverOverBase k K)) ι ≫ w).left := by
    intro A ι w
    rw [Over.comp_left, ← Category.assoc, ← Category.assoc]
    congr 1
    generalize_proofs
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (prodMap_id_left_comp_prodLeftIsoPullback k ι _).symm
  apply Over.OverMorphism.ext
  rw [← cancel_epi (Over.prodLeftIsoPullback (coverOverBase k K) (relationOverBase k K)).inv]
  apply pullback_relationOverBase_hom_ext
  · exact (key (relationInl k K) u).trans
      ((congrArg (fun f => _ ≫ Over.Hom.left f) hl).trans (key (relationInl k K) v).symm)
  · exact (key (relationInr k K) u).trans
      ((congrArg (fun f => _ ≫ Over.Hom.left f) hr).trans (key (relationInr k K) v).symm)

/-- A morphism into the self-product of the chart (read in schemes) is determined by its two
coordinates read through the splitting `coverSelfProductIso`. -/
private theorem comp_coverSelfProductIso_hom_eq (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) {Z : Scheme.{u}}
    {x : Z ⟶ (coverOverBase k K ⨯ coverOverBase k K).left} {y : Z ⟶ cover K ⨿ cover K}
    (hfst : x ≫ (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)).left =
      y ≫ (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.fst (coverMap k K) (coverMap k K))
    (hsnd : x ≫ (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)).left =
      y ≫ (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.snd (coverMap k K) (coverMap k K)) :
    x ≫ (coverSelfProductIso k K hdegree σ hσ).hom = y := by
  have e1 : (Over.prodLeftIsoPullback (coverOverBase k K) (coverOverBase k K)).hom ≫
      pullback.fst (coverMap k K) (coverMap k K) =
      (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  have e2 : (Over.prodLeftIsoPullback (coverOverBase k K) (coverOverBase k K)).hom ≫
      pullback.snd (coverMap k K) (coverMap k K) =
      (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  rw [← cancel_mono (coverFiberProductSplitIso k K hdegree σ hσ).inv, coverSelfProductIso,
    Iso.trans_hom, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · simpa only [Category.assoc, e1] using hfst
  · simpa only [Category.assoc, e2] using hsnd

/-- **A diagonal point of the self-product of the chart lies in its first summand.** Under the
splitting of the self-product, a point whose two coordinates agree is the point of the first
summand with that coordinate. -/
@[reassoc]
theorem prodLift_self_comp_coverSelfProductIso (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) {W : Over (base k)} (p : W ⟶ coverOverBase k K) :
    (prod.lift p p).left ≫ (coverSelfProductIso k K hdegree σ hσ).hom =
      p.left ≫ coprod.inl := by
  have hinlsnd : (coprod.inl : cover K ⟶ cover K ⨿ cover K) ≫
      (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.snd (coverMap k K) (coverMap k K) = 𝟙 (cover K) := by
    rw [← Category.assoc, coverFiberProductSplitIso_inl, pullback.diagonal_snd]
  apply comp_coverSelfProductIso_hom_eq
  · rw [← Over.comp_left, prod.lift_fst]
    simp [inl_comp_coverFiberProductSplitIso_inv_fst k K hdegree σ hσ]
  · rw [← Over.comp_left, prod.lift_snd]
    simp [hinlsnd]

/-- **A twisted point of the self-product of the chart lies in its second summand.** Under the
splitting of the self-product, a point whose second coordinate is the Galois twist of its first
is the point of the second summand with that first coordinate. -/
@[reassoc]
theorem prodLift_twist_comp_coverSelfProductIso (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) {W : Over (base k)} (p : W ⟶ coverOverBase k K) :
    (prod.lift p (p ≫ galoisActionOver k K σ)).left ≫
        (coverSelfProductIso k K hdegree σ hσ).hom =
      p.left ≫ coprod.inr := by
  apply comp_coverSelfProductIso_hom_eq
  · rw [← Over.comp_left, prod.lift_fst]
    simp [coverFiberProductSplitIso_inr_fst k K hdegree σ hσ]
  · rw [← Over.comp_left, prod.lift_snd, Over.comp_left, galoisActionOver_left]
    simp [coverFiberProductSplitIso_inr_snd k K hdegree σ hσ]

/-- **Jointly epic pair recognising the extra chart factor times the puncture.** Two morphisms
out of `U ×_S (U ∖ {0})` agree as soon as they agree on the two points of
`isPullback_puncturedSelfProduct`: the diagonal point `v ↦ (v, v)` and the twisted point
`v ↦ (σ(v), v)`, which are the two summands of that splitting. -/
private theorem prodMap_punctured_hom_ext (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) {T : Over (base k)}
    {u v : coverOverBase k K ⨯ coverPuncturedOverBase k K ⟶ T}
    (h1 : prod.lift (coverPuncturedInclusion k K) (𝟙 (coverPuncturedOverBase k K)) ≫ u =
      prod.lift (coverPuncturedInclusion k K) (𝟙 (coverPuncturedOverBase k K)) ≫ v)
    (h2 : prod.lift (coverPuncturedInclusion k K ≫ galoisActionOver k K σ)
          (𝟙 (coverPuncturedOverBase k K)) ≫ u =
      prod.lift (coverPuncturedInclusion k K ≫ galoisActionOver k K σ)
          (𝟙 (coverPuncturedOverBase k K)) ≫ v) :
    u = v := by
  have hinvfst : (Over.prodLeftIsoPullback (coverOverBase k K)
          (coverPuncturedOverBase k K)).inv ≫
      (prod.fst (X := coverOverBase k K) (Y := coverPuncturedOverBase k K)).left =
      pullback.fst (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K) :=
    Over.prodLeftIsoPullback_inv_fst _ _
  have hinvsnd : (Over.prodLeftIsoPullback (coverOverBase k K)
          (coverPuncturedOverBase k K)).inv ≫
      (prod.snd (X := coverOverBase k K) (Y := coverPuncturedOverBase k K)).left =
      pullback.snd (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K) :=
    Over.prodLeftIsoPullback_inv_snd _ _
  apply Over.OverMorphism.ext
  set a := prod.lift (coverPuncturedInclusion k K) (𝟙 (coverPuncturedOverBase k K)) with ha
  set b := prod.lift (coverPuncturedInclusion k K ≫ galoisActionOver k K σ)
    (𝟙 (coverPuncturedOverBase k K)) with hb
  have hkey : coprod.desc a.left b.left =
      (isPullback_puncturedSelfProduct k K hdegree σ hσ).isoPullback.hom ≫
        (Over.prodLeftIsoPullback (coverOverBase k K) (coverPuncturedOverBase k K)).inv := by
    apply prodLeft_hom_ext
    · rw [Category.assoc, hinvfst, IsPullback.isoPullback_hom_fst]
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, coprod.inl_desc, ha, ← Over.comp_left, prod.lift_fst]
        rfl
      · rw [coprod.inr_desc_assoc, coprod.inr_desc, hb, ← Over.comp_left, prod.lift_fst,
          Over.comp_left, galoisActionOver_left]
        rfl
    · rw [Category.assoc, hinvsnd, IsPullback.isoPullback_hom_snd]
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, coprod.inl_desc, ha, ← Over.comp_left, prod.lift_snd]
        rfl
      · rw [coprod.inr_desc_assoc, coprod.inr_desc, hb, ← Over.comp_left, prod.lift_snd]
        rfl
  have hepi : Epi (coprod.desc a.left b.left) := by
    rw [hkey]
    infer_instance
  rw [← cancel_epi (coprod.desc a.left b.left)]
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, coprod.inl_desc_assoc, ← Over.comp_left, ← Over.comp_left, h1]
  · rw [coprod.inr_desc_assoc, coprod.inr_desc_assoc, ← Over.comp_left, ← Over.comp_left, h2]

/-- **A reverse-twisted point of the self-product of the chart lies in its second summand.**
A point whose first coordinate is the Galois twist of its second is the point of the second
summand with that first coordinate, the Galois automorphism being an involution. -/
@[reassoc]
theorem prodLift_twist_left_comp_coverSelfProductIso (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) {W : Over (base k)} (p : W ⟶ coverOverBase k K) :
    (prod.lift (p ≫ galoisActionOver k K σ) p).left ≫
        (coverSelfProductIso k K hdegree σ hσ).hom =
      p.left ≫ galoisAction k K σ ≫ coprod.inr := by
  apply comp_coverSelfProductIso_hom_eq
  · rw [← Over.comp_left, prod.lift_fst, Over.comp_left, galoisActionOver_left]
    simp [coverFiberProductSplitIso_inr_fst k K hdegree σ hσ]
  · rw [← Over.comp_left, prod.lift_snd]
    simp [coverFiberProductSplitIso_inr_snd k K hdegree σ hσ,
      galoisAction_involutive k K hdegree σ]

/-- **The comparison map of part (6) is invariant under the base-changed relation.** The two
legs of `doubledRelation` have the same composite with `doubledSelfProductToGlued`, which is
the hypothesis the representability criterion of Stacks 03C5 consumes.

On the diagonal summand of the relation scheme both legs restrict to the identity, so there is
nothing to prove there. On the punctured summand one leg is the inclusion of the puncture and
the other that inclusion followed by the Galois automorphism; splitting `U ×_S (U ∖ {0})` into
its two copies of the puncture with `isPullback_puncturedSelfProduct`, on each copy the two
legs land in the two different charts of the gluing datum, which agree on the puncture by
`Stacks.Examples.doubleSectionCover_chart_agree`. -/
theorem doubledRelation_comp_doubledSelfProductToGlued (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (doubledRelation k K σ).target ≫ doubledSelfProductToGlued k K hdegree σ hσ =
      (doubledRelation k K σ).source ≫ doubledSelfProductToGlued k K hdegree σ hσ := by
  have hinv : galoisActionOver k K σ ≫ galoisActionOver k K σ = 𝟙 (coverOverBase k K) := by
    apply Over.OverMorphism.ext
    simpa using galoisAction_involutive k K hdegree σ
  rw [doubledRelation_target, doubledRelation_source]
  apply prodMap_relation_hom_ext
  · rw [prod.map_map_assoc, prod.map_map_assoc, relationInl_relationFirst,
      relationInl_relationSecond]
  · rw [prod.map_map_assoc, prod.map_map_assoc, relationInr_relationFirst,
      relationInr_relationSecond]
    apply prodMap_punctured_hom_ext k K hdegree σ hσ
    · rw [prod.lift_map_assoc, prod.lift_map_assoc]
      simp only [Category.comp_id, Category.id_comp]
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, doubledSelfProductToGlued, coverSelfProductOverIso,
        Over.isoMk_hom_left, doubledChartsToGluedOverBase, Over.homMk_left,
        coverPuncturedInclusion]
      rw [prodLift_self_comp_coverSelfProductIso_assoc k K hdegree σ hσ,
        prodLift_twist_comp_coverSelfProductIso_assoc k K hdegree σ hσ, doubledChartsToGlued,
        coprod.inl_desc, coprod.inr_desc]
      exact Stacks.Examples.doubleSectionCover_chart_agree (cover K) (puncturedCover K)
    · rw [prod.lift_map_assoc, prod.lift_map_assoc]
      simp only [Category.comp_id, Category.id_comp]
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, doubledSelfProductToGlued, coverSelfProductOverIso,
        Over.isoMk_hom_left, doubledChartsToGluedOverBase, Over.homMk_left,
        coverPuncturedInclusion]
      rw [prodLift_twist_left_comp_coverSelfProductIso_assoc k K hdegree σ hσ,
        prodLift_self_comp_coverSelfProductIso_assoc k K hdegree σ hσ, doubledChartsToGlued,
        coprod.inl_desc, coprod.inr_desc, Over.comp_left, galoisActionOver_left]
      have key : ((puncturedCover K).ι ≫ galoisAction k K σ) ≫
            (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart false =
          ((puncturedCover K).ι ≫ galoisAction k K σ) ≫
            (Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)).chart true := by
        rw [← galoisActionPuncturedMap_ι k K σ, Category.assoc, Category.assoc,
          Stacks.Examples.doubleSectionCover_chart_agree (cover K) (puncturedCover K)]
      exact key

end AlgebraicGeometry.TwistedDoubledOrigin

end
