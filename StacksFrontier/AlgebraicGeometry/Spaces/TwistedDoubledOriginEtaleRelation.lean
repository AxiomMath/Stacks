module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelationFromInvolution
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSelfProduct
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Slice

/-!
# The relation of the twisted doubled origin is an étale equivalence relation

Let `K/k` be a degree two Galois extension with nonidentity automorphism `σ`, let
`S = Spec k[x]` and `U = Spec K[x]`, and let `R = Δ(U) ⨿ Δ'(U ∖ {0})` be the relation of the
twisted doubled origin, with its two projections to `U` over `S`.  This file proves that
`R ⟶ U ×_S U` is an étale equivalence relation.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.relationToSelfProduct` exhibits the relation scheme
  inside the self-product `U ×_S U` of the chart over the base.
* `AlgebraicGeometry.TwistedDoubledOrigin.coverSelfProductIso` is the same splitting read on the
  underlying scheme of the categorical product of the chart with itself in the slice category
  over the base.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.relationToSelfProduct_eq`: through the splitting
  `U ×_S U ≅ U ⨿ U` the relation is the inclusion `U ⨿ (U ∖ {0}) ⟶ U ⨿ U`, so it is an open
  immersion; in particular it is a monomorphism, which is the joint monicity
  `AlgebraicGeometry.TwistedDoubledOrigin.jointlyMono₂_relationFirst_relationSecond` of the
  two projections.
* `AlgebraicGeometry.TwistedDoubledOrigin.twistedRelation_left_comp_coverSelfProductIso`: the
  same description for the morphism of slices, from which
  `AlgebraicGeometry.TwistedDoubledOrigin.isOpenImmersion_twistedRelation_left` and
  `AlgebraicGeometry.TwistedDoubledOrigin.isAffineHom_twistedRelation_left` read off that the
  relation is an affine open immersion into the self-product of the chart;
  `AlgebraicGeometry.TwistedDoubledOrigin.isAffine_coverOverBase_prod` says that that
  self-product is itself affine.
* `AlgebraicGeometry.TwistedDoubledOrigin.twistedRelation_isEtaleEquivalenceRelation`:
  **Stacks 03FN**, the relation of the twisted doubled origin is an étale equivalence
  relation on the chart over the base.

## Implementation notes

The equivalence-relation property is an instance of
`AlgebraicGeometry.isEquivalenceRelation_of_coprod_involution`, which needs only that the
Galois automorphism of the chart is an involution preserving the puncture; the degree
hypothesis enters twice, once through that involutivity and once through the splitting of the
self-product which gives joint monicity.  The passage from the two bare morphisms of schemes
to the two morphisms of schemes over the base is
`CategoryTheory.isEquivalenceRelation_of_left`.

Étaleness of the two projections is checked summand by summand with
`AlgebraicGeometry.etale_coprod`: on the diagonal summand each is the identity, and on the
twisted summand they are the inclusion of the puncture and that inclusion followed by the
Galois automorphism of the chart, which is an isomorphism.

The binary product of the chart with itself in `CategoryTheory.Over (Spec k[x])` has the fibre
product `U ×_S U` as its underlying scheme, by `CategoryTheory.Over.prodLeftIsoPullback`;
composing that comparison with the splitting of the fibre product gives
`AlgebraicGeometry.TwistedDoubledOrigin.coverSelfProductIso`.  Affineness of the relation is
affineness of its source and of its target: the source is the disjoint union of the chart with
the puncture `D(x)`, a principal open of an affine scheme, and the target is the disjoint union
of two copies of the chart.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The puncture of the chart is affine, being a principal open of an affine scheme. -/
instance isAffine_puncturedCover : IsAffine (puncturedCover K).toScheme :=
  IsAffineOpen.Spec_basicOpen (R := .of (Polynomial K)) _

/-- The relation scheme inside the self-product of the chart over the base: the two
projections of the relation agree over the base, so they factor through `U ×_S U`. -/
def relationToSelfProduct (σ : K ≃ₐ[k] K) :
    relationScheme K ⟶ pullback (coverMap k K) (coverMap k K) :=
  pullback.lift (relationFirst k K).left (relationSecond k K σ).left
    ((relationFirst k K).w.trans (relationSecond k K σ).w.symm)

/-- The first projection of the relation is the splitting of the self-product composed with the
first projection. -/
private theorem relationFirst_left_eq [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (relationFirst k K).left =
      (coprod.map (𝟙 (cover K)) (puncturedCover K).ι ≫
        (coverFiberProductSplitIso k K hdegree σ hσ).inv) ≫
          pullback.fst (coverMap k K) (coverMap k K) := by
  refine coprod.hom_ext ?_ ?_
  · rw [relationFirst_inl, ← Category.assoc, ← Category.assoc, coprod.inl_map,
      Category.id_comp, coverFiberProductSplitIso_inl, pullback.diagonal_fst]
  · rw [relationFirst_inr, ← Category.assoc, ← Category.assoc, coprod.inr_map,
      Category.assoc, Category.assoc, coverFiberProductSplitIso_inr_fst, Category.comp_id]

/-- The second projection of the relation is the splitting of the self-product composed with the
second projection. -/
private theorem relationSecond_left_eq [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (relationSecond k K σ).left =
      (coprod.map (𝟙 (cover K)) (puncturedCover K).ι ≫
        (coverFiberProductSplitIso k K hdegree σ hσ).inv) ≫
          pullback.snd (coverMap k K) (coverMap k K) := by
  refine coprod.hom_ext ?_ ?_
  · rw [relationSecond_inl, ← Category.assoc, ← Category.assoc, coprod.inl_map,
      Category.id_comp, coverFiberProductSplitIso_inl, pullback.diagonal_snd]
  · rw [relationSecond_inr, ← Category.assoc, ← Category.assoc, coprod.inr_map,
      Category.assoc, Category.assoc, coverFiberProductSplitIso_inr_snd]

/-- Read through the splitting `U ×_S U ≅ U ⨿ U` of the self-product, the relation scheme is
the inclusion of `U ⨿ (U ∖ {0})`: the first summand is the diagonal and the second is the
twisted diagonal away from the origin. -/
theorem relationToSelfProduct_eq [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    relationToSelfProduct k K σ =
      coprod.map (𝟙 (cover K)) (puncturedCover K).ι ≫
        (coverFiberProductSplitIso k K hdegree σ hσ).inv := by
  refine pullback.hom_ext ?_ ?_
  · rw [relationToSelfProduct, pullback.lift_fst]
    exact relationFirst_left_eq k K hdegree σ hσ
  · rw [relationToSelfProduct, pullback.lift_snd]
    exact relationSecond_left_eq k K hdegree σ hσ

/-- The relation scheme is an open subscheme of the self-product of the chart over the
base. -/
theorem isOpenImmersion_relationToSelfProduct [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    IsOpenImmersion (relationToSelfProduct k K σ) := by
  rw [relationToSelfProduct_eq k K hdegree σ hσ]
  infer_instance

/-- The two projections of the relation of the twisted doubled origin are jointly monic: the
relation is a subscheme of the self-product of the chart over the base. -/
theorem jointlyMono₂_relationFirst_relationSecond [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    JointlyMono₂ (relationFirst k K).left (relationSecond k K σ).left := by
  have : Mono (relationToSelfProduct k K σ) :=
    have := isOpenImmersion_relationToSelfProduct k K hdegree σ hσ
    inferInstance
  refine ⟨fun T f g h₁ h₂ => (cancel_mono (relationToSelfProduct k K σ)).1 ?_⟩
  refine pullback.hom_ext ?_ ?_
  · simpa only [relationToSelfProduct, Category.assoc, pullback.lift_fst] using h₁
  · simpa only [relationToSelfProduct, Category.assoc, pullback.lift_snd] using h₂

/-- The first projection of the relation of the twisted doubled origin is étale: it is the
identity on the diagonal summand and the inclusion of the puncture on the twisted summand. -/
theorem etale_relationFirst : Etale (relationFirst k K).left :=
  etale_coprod _ _ inferInstance inferInstance

/-- The second projection of the relation of the twisted doubled origin is étale: it is the
identity on the diagonal summand and, on the twisted summand, the inclusion of the puncture
followed by the automorphism of the chart induced by `σ`. -/
theorem etale_relationSecond (σ : K ≃ₐ[k] K) : Etale (relationSecond k K σ).left :=
  etale_coprod _ _ inferInstance inferInstance

/-- The self-product of the chart in the slice category over the base, split as the disjoint
union of the diagonal and the twisted diagonal. -/
def coverSelfProductIso [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coverOverBase k K ⨯ coverOverBase k K).left ≅ cover K ⨿ cover K :=
  Over.prodLeftIsoPullback (coverOverBase k K) (coverOverBase k K) ≪≫
    coverFiberProductSplitIso k K hdegree σ hσ

/-- **Stacks 03FN.** Under the splitting of the self-product of the chart, the relation is the
identity on the diagonal summand and the inclusion of the puncture on the twisted summand. -/
theorem twistedRelation_left_comp_coverSelfProductIso [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (twistedRelation k K σ).left ≫ (coverSelfProductIso k K hdegree σ hσ).hom =
      coprod.map (𝟙 (cover K)) (puncturedCover K).ι := by
  have htgt : (twistedRelation k K σ ≫ prod.fst) = relationFirst k K :=
    twistedRelation_target k K σ
  have hsrc : (twistedRelation k K σ ≫ prod.snd) = relationSecond k K σ :=
    twistedRelation_source k K σ
  have key : (twistedRelation k K σ).left ≫
      (Over.prodLeftIsoPullback (coverOverBase k K) (coverOverBase k K)).hom =
      coprod.map (𝟙 (cover K)) (puncturedCover K).ι ≫
        (coverFiberProductSplitIso k K hdegree σ hσ).inv := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc,
        Over.prodLeftIsoPullback_hom_fst (coverOverBase k K) (coverOverBase k K),
        ← Over.comp_left,
        htgt]
      exact relationFirst_left_eq k K hdegree σ hσ
    · rw [Category.assoc,
        Over.prodLeftIsoPullback_hom_snd (coverOverBase k K) (coverOverBase k K),
        ← Over.comp_left,
        hsrc]
      exact relationSecond_left_eq k K hdegree σ hσ
  rw [coverSelfProductIso, Iso.trans_hom, ← Category.assoc, key, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The relation, read inside the self-product of the chart. -/
private theorem twistedRelation_left_eq [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (twistedRelation k K σ).left =
      coprod.map (𝟙 (cover K)) (puncturedCover K).ι ≫
        (coverSelfProductIso k K hdegree σ hσ).inv := by
  rw [← twistedRelation_left_comp_coverSelfProductIso k K hdegree σ hσ, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **Stacks 03FN.** The relation is an open immersion into the self-product of the chart: under
the splitting of that self-product it is the identity on one summand and the inclusion of the
puncture on the other. -/
theorem isOpenImmersion_twistedRelation_left [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    IsOpenImmersion (twistedRelation k K σ).left := by
  rw [twistedRelation_left_eq k K hdegree σ hσ]
  have : IsOpenImmersion (coprod.map (𝟙 (cover K)) (puncturedCover K).ι) :=
    IsZariskiLocalAtTarget.coprodMap (P := @IsOpenImmersion.{u}) _ _ inferInstance inferInstance
  infer_instance

/-- **Stacks 03FN.** The self-product of the chart over the base is affine, being the disjoint
union of two affine lines. -/
theorem isAffine_coverOverBase_prod [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    IsAffine (coverOverBase k K ⨯ coverOverBase k K).left :=
  IsAffine.of_isIso (coverSelfProductIso k K hdegree σ hσ).hom

/-- **Stacks 03FN.** The relation is an affine morphism into the self-product of the chart, the
puncture being the affine principal open `D(x)`. -/
theorem isAffineHom_twistedRelation_left [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    IsAffineHom (twistedRelation k K σ).left :=
  have : IsAffine (relationOverBase k K).left :=
    show IsAffine (relationScheme K) from inferInstance
  have := isAffine_coverOverBase_prod k K hdegree σ hσ
  isAffineHom_of_isAffine _

/-- **Stacks 03FN.** The diagonal of the chart together with the twisted diagonal away from
the origin is an étale equivalence relation on the chart over the base. -/
@[stacks 03FN "etale_relation"]
theorem twistedRelation_isEtaleEquivalenceRelation [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (twistedRelation k K σ) := by
  have hjm : JointlyMono₂ (relationFirst k K).left (relationSecond k K σ).left :=
    jointlyMono₂_relationFirst_relationSecond k K hdegree σ hσ
  have hleft : IsEquivalenceRelation (relationFirst k K).left (relationSecond k K σ).left :=
    isEquivalenceRelation_of_coprod_involution (puncturedCover K).ι (galoisAction k K σ)
      (galoisActionPuncturedMap k K σ) _ _ (relationFirst_inl k K) (relationFirst_inr k K)
      (relationSecond_inl k K σ) (relationSecond_inr k K σ)
      (galoisActionPuncturedMap_ι k K σ) (galoisAction_involutive k K hdegree σ)
  have hover : IsEquivalenceRelation (relationFirst k K) (relationSecond k K σ) :=
    isEquivalenceRelation_of_left _ _
  have : IsEquivalenceRelation (twistedRelation k K σ).target
      (twistedRelation k K σ).source := by
    rw [twistedRelation_target, twistedRelation_source]
    exact hover
  refine { etale_source := ?_, etale_target := ?_ }
  · rw [twistedRelation_source]
    exact etale_relationSecond k K σ
  · rw [twistedRelation_target]
    exact etale_relationFirst k K

end AlgebraicGeometry.TwistedDoubledOrigin

end
