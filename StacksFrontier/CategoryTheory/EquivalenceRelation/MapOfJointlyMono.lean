module

public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer

/-!
# Pushing an internal equivalence relation forward without preserving products

A functor `G` carries an internal equivalence relation `p₁ p₂ : R ⟶ X` to an internal equivalence
relation `G.map p₁, G.map p₂` as soon as the image pair is jointly monic and the image of the
limiting pullback cone of the transitivity datum is limiting; in particular it does so when `G`
preserves pullbacks and the image pair is jointly monic. Neither statement asks `G` to preserve
binary products.

## Main definitions

* `CategoryTheory.TransitiveRelation.mapCone`: the image of the transitivity datum's limiting
  cone, as a cone over the image cospan.

## Main results

* `CategoryTheory.jointlyMono₂_iff_mono_prodLift`: joint monicity of a pair is monicity of its
  lift into the product.
* `CategoryTheory.isEquivalenceRelation_map_of_jointlyMono₂`: a functor preserving pullbacks
  carries an internal equivalence relation to one, as soon as the image pair is jointly monic.
* `CategoryTheory.isEquivalenceRelation_map_of_jointlyMono₂_of_isLimit`: a functor carries an
  internal equivalence relation to one, given joint monicity of the image pair and that
  `CategoryTheory.TransitiveRelation.mapCone` is limiting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A pair of morphisms is jointly monic if and only if its lift into the product is a
monomorphism. -/
theorem jointlyMono₂_iff_mono_prodLift [HasBinaryProducts C] {R X : C} (p₁ p₂ : R ⟶ X) :
    JointlyMono₂ p₁ p₂ ↔ Mono (prod.lift p₁ p₂) :=
  ⟨fun h ↦ ⟨fun a b hab ↦ h.right_cancellation a b (by simpa using congrArg (· ≫ prod.fst) hab)
      (by simpa using congrArg (· ≫ prod.snd) hab)⟩,
    fun _ ↦ ⟨fun _ a b h₁ h₂ ↦ (cancel_mono (prod.lift p₁ p₂)).mp
      (prod.hom_ext (by simpa using h₁) (by simpa using h₂))⟩⟩

/-- A functor preserving pullbacks carries an internal equivalence relation to an internal
equivalence relation, as soon as the image pair is jointly monic. -/
theorem isEquivalenceRelation_map_of_jointlyMono₂ (G : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan G] {R X : C} (p₁ p₂ : R ⟶ X)
    (h : IsEquivalenceRelation p₁ p₂)
    (hjm : JointlyMono₂ (G.map p₁) (G.map p₂)) :
    IsEquivalenceRelation (G.map p₁) (G.map p₂) := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  have := hjm
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := e.toReflexiveRelation.map G
      __ := e.toSymmetricRelation.map G
      __ := e.toTransitiveRelation.map G }

/-- The image under a functor of the limiting cone carried by a transitivity datum, as a cone
over the image cospan. -/
def TransitiveRelation.mapCone (G : C ⥤ D) {R X : C} {p₁ p₂ : R ⟶ X}
    (et : TransitiveRelation p₁ p₂) : PullbackCone (G.map p₂) (G.map p₁) :=
  PullbackCone.mk (G.map et.c.fst) (G.map et.c.snd) <| by
    simpa using congrArg G.map et.c.condition

/-- A functor carries an internal equivalence relation to an internal equivalence relation as
soon as the image pair is jointly monic and the image `CategoryTheory.TransitiveRelation.mapCone`
of the limiting cone of the transitivity datum is limiting. -/
theorem isEquivalenceRelation_map_of_jointlyMono₂_of_isLimit (G : C ⥤ D)
    {R X : C} {p₁ p₂ : R ⟶ X} (e : EquivalenceRelation p₁ p₂)
    (hjm : JointlyMono₂ (G.map p₁) (G.map p₂))
    (hc : IsLimit (e.toTransitiveRelation.mapCone G)) :
    IsEquivalenceRelation (G.map p₁) (G.map p₂) :=
  EquivalenceRelation.isEquivalenceRelation
    { toJointlyMono₂ := hjm
      r := G.map e.r
      reflexivity₁ := by rw [← G.map_comp, e.reflexivity₁, G.map_id]
      reflexivity₂ := by rw [← G.map_comp, e.reflexivity₂, G.map_id]
      s := G.map e.s
      symmetry₁ := by rw [← G.map_comp, e.symmetry₁]
      symmetry₂ := by rw [← G.map_comp, e.symmetry₂]
      c := e.toTransitiveRelation.mapCone G
      isLimit := hc
      t := G.map e.t
      transitivity₁ := by
        show G.map e.t ≫ G.map p₁ = G.map e.c.fst ≫ G.map p₁
        rw [← G.map_comp, ← G.map_comp, e.transitivity₁]
      transitivity₂ := by
        show G.map e.t ≫ G.map p₂ = G.map e.c.snd ≫ G.map p₂
        rw [← G.map_comp, ← G.map_comp, e.transitivity₂] }

end CategoryTheory

end
