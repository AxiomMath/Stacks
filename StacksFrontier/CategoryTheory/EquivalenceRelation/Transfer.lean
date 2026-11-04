module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Transferring an internal equivalence relation along a functor

An internal equivalence relation is a pair of parallel morphisms together with reflexivity,
symmetry and transitivity morphisms and the requirement that the pair be jointly monic. All
of that data is preserved by a functor, and the joint monicity is the only part which is not:
it is a condition on *all* test objects of the target category. This file records the three
transfers which make an internal equivalence relation available in a different category:

* *forgetting a slice*, from `CategoryTheory.Over X` to the ambient category;
* *reflecting* along a fully faithful functor, up to an isomorphism of the relation object;
* *pushing forward* along a functor preserving binary products and pullbacks, where joint
  monicity is monicity of the induced morphism to the product and therefore transfers.

## Main definitions

* `CategoryTheory.EquivalenceRelation.reflect` is the internal equivalence relation obtained
  by reflecting one along a fully faithful functor.

## Main results

* `CategoryTheory.jointlyMono₂_left` and `CategoryTheory.isEquivalenceRelation_left`: the
  underlying pair of morphisms of a jointly monic pair, respectively of an internal
  equivalence relation, in a slice category is again one.
* `CategoryTheory.isEquivalenceRelation_of_map` and
  `CategoryTheory.isEquivalenceRelation_of_map_of_iso`: a pair of parallel morphisms whose
  image under a fully faithful functor is an internal equivalence relation is one, the second
  allowing the image of the relation object to be named only up to isomorphism.
* `CategoryTheory.jointlyMono₂_map` and `CategoryTheory.isEquivalenceRelation_map`: a jointly
  monic pair, respectively an internal equivalence relation, is carried to one by a functor
  preserving binary products and pullbacks.

## Implementation notes

Joint monicity in a slice category transfers to the ambient category because a test morphism
`f : Y ⟶ R.left` is itself a morphism of the slice from `Over.mk (f ≫ R.hom)`, and its
competitor lies over the same structure morphism as soon as the two agree after one of the
projections. This is the converse of `CategoryTheory.jointlyMono₂_of_left`.

Reflection needs a pullback of the pair in the source category — the transitivity datum of an
internal equivalence relation carries a *limiting* cone, which cannot be manufactured from the
image — but it does not need the functor to preserve that pullback: the image of the chosen
cone is a cone over the image pair, and the limiting cone carried by the image relation
receives it. Reflexivity, symmetry and transitivity are then preimages of composites, and
joint monicity and the three identities follow from faithfulness.

Pushing forward is the argument of
`AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback` in general form: joint monicity
of `p₁, p₂` is monicity of `prod.lift p₁ p₂`, a functor preserving pullbacks preserves
monomorphisms, and a functor preserving binary products identifies the image of the product
with the product of the images.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-! ### Forgetting a slice -/

/-- The underlying pair of morphisms of a jointly monic pair in a slice category is jointly
monic: a test morphism into the underlying object of the source is a morphism of the slice. -/
theorem jointlyMono₂_left {X : C} {R U : Over X} (p₁ p₂ : R ⟶ U) [JointlyMono₂ p₁ p₂] :
    JointlyMono₂ p₁.left p₂.left where
  right_cancellation Y f g h₁ h₂ := by
    have hw : p₁.left ≫ U.hom = R.hom := Over.w p₁
    have hg : g ≫ R.hom = f ≫ R.hom := by
      rw [← hw, ← Category.assoc, ← h₁, Category.assoc, hw]
    have h := JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂)
      (Y := Over.mk (f ≫ R.hom)) (Over.homMk f rfl) (Over.homMk g hg)
      (Over.OverMorphism.ext (by simpa using h₁)) (Over.OverMorphism.ext (by simpa using h₂))
    simpa using congrArg Over.Hom.left h

/-- The underlying pair of morphisms of an internal equivalence relation in a slice category is
an internal equivalence relation: the projection to the ambient category is faithful and
preserves pullbacks. -/
theorem isEquivalenceRelation_left {X : C} {R U : Over X} (p₁ p₂ : R ⟶ U)
    (h : IsEquivalenceRelation p₁ p₂) : IsEquivalenceRelation p₁.left p₂.left := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  have _ : JointlyMono₂ p₁ p₂ := ⟨e.right_cancellation⟩
  have _ : JointlyMono₂ ((Over.forget X).map p₁) ((Over.forget X).map p₂) :=
    jointlyMono₂_left p₁ p₂
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := e.toReflexiveRelation.map (Over.forget X)
      __ := e.toSymmetricRelation.map (Over.forget X)
      __ := e.toTransitiveRelation.map (Over.forget X) }

/-! ### Reflecting along a fully faithful functor -/

/-- Reflect an internal equivalence relation along a fully faithful functor: if the image of a
pair of parallel morphisms, precomposed with an isomorphism of the relation object, carries an
internal equivalence relation, then so does the pair itself. The chosen pullback of the pair
provides the limiting cone of the transitivity datum. -/
noncomputable def EquivalenceRelation.reflect (F : C ⥤ D) [F.Full] [F.Faithful] {R X : C}
    {A : D} (i : A ≅ F.obj R) (p₁ p₂ : R ⟶ X) [HasPullback p₂ p₁]
    (e : EquivalenceRelation (i.hom ≫ F.map p₁) (i.hom ≫ F.map p₂)) :
    EquivalenceRelation p₁ p₂ :=
  let er := e.toReflexiveRelation
  let es := e.toSymmetricRelation
  let et := e.toTransitiveRelation
  have hcond : (F.map (pullback.fst p₂ p₁) ≫ i.inv) ≫ i.hom ≫ F.map p₂ =
      (F.map (pullback.snd p₂ p₁) ≫ i.inv) ≫ i.hom ≫ F.map p₁ := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp]
    exact congrArg F.map pullback.condition
  let k := PullbackCone.IsLimit.lift et.isLimit (F.map (pullback.fst p₂ p₁) ≫ i.inv)
    (F.map (pullback.snd p₂ p₁) ≫ i.inv) hcond
  have hkfst : k ≫ et.c.fst = F.map (pullback.fst p₂ p₁) ≫ i.inv :=
    PullbackCone.IsLimit.lift_fst _ _ _ _
  have hksnd : k ≫ et.c.snd = F.map (pullback.snd p₂ p₁) ≫ i.inv :=
    PullbackCone.IsLimit.lift_snd _ _ _ _
  { right_cancellation Y f g h₁ h₂ := by
      apply F.map_injective
      have hfg : F.map f ≫ i.inv = F.map g ≫ i.inv := by
        refine e.right_cancellation _ _ ?_ ?_
        · simpa using congrArg F.map h₁
        · simpa using congrArg F.map h₂
      simpa using congrArg (· ≫ i.hom) hfg
    r := F.preimage (er.r ≫ i.hom)
    reflexivity₁ := by
      apply F.map_injective
      simp only [F.map_comp, F.map_preimage]
      rw [Category.assoc, er.reflexivity₁, F.map_id]
    reflexivity₂ := by
      apply F.map_injective
      simp only [F.map_comp, F.map_preimage]
      rw [Category.assoc, er.reflexivity₂, F.map_id]
    s := F.preimage (i.inv ≫ es.s ≫ i.hom)
    symmetry₁ := by
      apply F.map_injective
      simp only [F.map_comp, F.map_preimage]
      rw [Category.assoc, Category.assoc, es.symmetry₁, Iso.inv_hom_id_assoc]
    symmetry₂ := by
      apply F.map_injective
      simp only [F.map_comp, F.map_preimage]
      rw [Category.assoc, Category.assoc, es.symmetry₂, Iso.inv_hom_id_assoc]
    c := pullback.cone p₂ p₁
    isLimit := pullback.isLimit p₂ p₁
    t := F.preimage (k ≫ et.t ≫ i.hom)
    transitivity₁ := by
      apply F.map_injective
      simp only [F.map_comp, F.map_preimage]
      rw [Category.assoc, Category.assoc, et.transitivity₁, ← Category.assoc, hkfst]
      simp
    transitivity₂ := by
      apply F.map_injective
      simp only [F.map_comp, F.map_preimage]
      rw [Category.assoc, Category.assoc, et.transitivity₂, ← Category.assoc, hksnd]
      simp }

/-- A pair of parallel morphisms whose image under a fully faithful functor, precomposed with an
isomorphism of the relation object, is an internal equivalence relation is itself an internal
equivalence relation. -/
theorem isEquivalenceRelation_of_map_of_iso (F : C ⥤ D) [F.Full] [F.Faithful] {R X : C}
    {A : D} (i : A ≅ F.obj R) (p₁ p₂ : R ⟶ X) [HasPullback p₂ p₁]
    (h : IsEquivalenceRelation (i.hom ≫ F.map p₁) (i.hom ≫ F.map p₂)) :
    IsEquivalenceRelation p₁ p₂ :=
  (EquivalenceRelation.reflect F i p₁ p₂
    h.nonempty_equivalenceRelation.some).isEquivalenceRelation

/-- A pair of parallel morphisms whose image under a fully faithful functor is an internal
equivalence relation is itself an internal equivalence relation. -/
theorem isEquivalenceRelation_of_map (F : C ⥤ D) [F.Full] [F.Faithful] {R X : C}
    (p₁ p₂ : R ⟶ X) [HasPullback p₂ p₁]
    (h : IsEquivalenceRelation (F.map p₁) (F.map p₂)) : IsEquivalenceRelation p₁ p₂ :=
  isEquivalenceRelation_of_map_of_iso F (Iso.refl (F.obj R)) p₁ p₂ (by simpa using h)

/-! ### Pushing forward along a functor preserving finite limits -/

/-- A functor preserving binary products and pullbacks carries a jointly monic pair to a jointly
monic pair: joint monicity is monicity of the morphism to the product. -/
theorem jointlyMono₂_map (G : C ⥤ D) [HasBinaryProducts C]
    [PreservesLimitsOfShape (Discrete WalkingPair) G] [PreservesLimitsOfShape WalkingCospan G]
    {R X : C} (p₁ p₂ : R ⟶ X) (h : JointlyMono₂ p₁ p₂) :
    JointlyMono₂ (G.map p₁) (G.map p₂) := by
  have _ : Mono (prod.lift p₁ p₂) := ⟨fun a b hab => h.right_cancellation a b
    (by simpa using congrArg (· ≫ prod.fst) hab) (by simpa using congrArg (· ≫ prod.snd) hab)⟩
  have _ : Mono (G.map (prod.lift p₁ p₂)) := preserves_mono_of_preservesLimit G _
  refine ⟨fun _ a b h₁ h₂ => (cancel_mono (G.map (prod.lift p₁ p₂))).mp
    ((cancel_mono (PreservesLimitPair.iso G X X).hom).mp (prod.hom_ext ?_ ?_))⟩
  · simpa [PreservesLimitPair.iso_hom, ← G.map_comp] using h₁
  · simpa [PreservesLimitPair.iso_hom, ← G.map_comp] using h₂

/-- A functor preserving binary products and pullbacks carries an internal equivalence relation
to an internal equivalence relation. -/
@[sga "4 I 10.9" "more general"]
theorem isEquivalenceRelation_map (G : C ⥤ D) [HasBinaryProducts C]
    [PreservesLimitsOfShape (Discrete WalkingPair) G] [PreservesLimitsOfShape WalkingCospan G]
    {R X : C} (p₁ p₂ : R ⟶ X) (h : IsEquivalenceRelation p₁ p₂) :
    IsEquivalenceRelation (G.map p₁) (G.map p₂) := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  have _ : JointlyMono₂ (G.map p₁) (G.map p₂) :=
    jointlyMono₂_map G p₁ p₂ ⟨e.right_cancellation⟩
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := e.toReflexiveRelation.map G
      __ := e.toSymmetricRelation.map G
      __ := e.toTransitiveRelation.map G }

end CategoryTheory

end
