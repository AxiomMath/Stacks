module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.CategoryTheory.Limits.BinaryCoproductDescent

/-!
# The graph of a free involution on a subobject is an equivalence relation

Let `X` be an object of a finitary extensive category with pullbacks, let `i : V ⟶ X` be a
monomorphism, and let `a : X ⟶ X` be an involution which preserves `V`, in the sense that it
is covered by an endomorphism `b : V ⟶ V` with `b ≫ i = i ≫ a`. Suppose further that `a`
acts *freely* on `V`: no object maps to `V` in a way that `i` and `i ≫ a` cannot tell apart.

Then the two morphisms

  `X ⨿ V ⇉ X`,   `coprod.desc (𝟙 X) i`  and  `coprod.desc (𝟙 X) (i ≫ a)`,

the diagonal together with the graph of `a` restricted to `V`, form an internal equivalence
relation on `X`.

This is the relation of [Stacks, Tag 02Z1] and [Stacks, Tag 087I], where `X` is an affine
scheme, `V` an open subscheme, and `a` the reflection in a point.

## Main results

* `CategoryTheory.jointlyMono₂_coprod_desc_of_free_involution`: the two morphisms are jointly
  monomorphic, that is the relation is a relation and not merely a pre-relation.
* `CategoryTheory.isEquivalenceRelation_coprod_desc_of_free_involution`: they form an
  equivalence relation.

## References

* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 087I](https://stacks.math.columbia.edu/tag/087I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

/-- If `f ≫ p = g ≫ q`, then restricting along `k ≫ j` transports the equation to any
factorizations `j ≫ f = x` and `k ≫ j ≫ g = y`. -/
private theorem comp_comp_eq_of_comp_eq {C : Type u} [Category.{v} C] {T Z W R S : C}
    {f g : T ⟶ R} {p q : R ⟶ S} (h : f ≫ p = g ≫ q) (k : Z ⟶ W) (j : W ⟶ T) {x : W ⟶ R} {y : Z ⟶ R}
    (hj : j ≫ f = x) (hk : k ≫ j ≫ g = y) : (k ≫ x) ≫ p = y ≫ q := by
  subst hj hk
  simp only [Category.assoc, h]

variable {C : Type u} [Category.{v} C] [FinitaryExtensive C] [HasPullbacks C]

/-- **The diagonal together with the graph of a free involution is a relation.** For a
monomorphism `i : V ⟶ X` and an endomorphism `a : X ⟶ X` acting freely on `V`, the two
morphisms `coprod.desc (𝟙 X) i` and `coprod.desc (𝟙 X) (i ≫ a)` out of `X ⨿ V` are jointly
monomorphic. -/
theorem jointlyMono₂_coprod_desc_of_free_involution {X V : C} (i : V ⟶ X) [Mono i]
    (a : X ⟶ X)
    (hfree : ∀ {T : C} (b : T ⟶ V), b ≫ i = b ≫ i ≫ a → Subsingleton (T ⟶ X ⨿ V)) :
    JointlyMono₂ (coprod.desc (𝟙 X) i) (coprod.desc (𝟙 X) (i ≫ a)) := by
  refine ⟨fun _ f g ht hs => ?_⟩
  refine hom_ext_of_coprod_cases f f g (fun W j b hj => ?_) (fun W j b hj => ?_) <;>
    refine hom_ext_of_coprod_cases (j ≫ g) (j ≫ f) (j ≫ g)
      (fun Z l c hl => ?_) (fun Z l c hl => ?_) <;>
    have ht' := comp_comp_eq_of_comp_eq ht l j hj hl <;>
    have hs' := comp_comp_eq_of_comp_eq hs l j hj hl <;>
    simp only [← Category.assoc, hj, hl] <;>
    simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, Category.comp_id] at ht' hs'
  · simp only [ht']
  · exact @Subsingleton.elim _ (hfree c (ht'.symm.trans hs')) _ _
  · exact @Subsingleton.elim _ (hfree (l ≫ b) (by simpa using ht'.trans hs'.symm)) _ _
  · rw [(cancel_mono i).mp (by rwa [Category.assoc] : (l ≫ b) ≫ i = c ≫ i)]

/-- **The transitivity lift for the diagonal together with the graph of an involution.** A
pair of morphisms `f, g : T ⟶ X ⨿ V` with the source of `f` equal to the target of `g`
composes: there is a third morphism whose target is the target of `f` and whose source is the
source of `g`. -/
theorem exists_lift_coprod_desc_of_involution {X V T : C} (i : V ⟶ X) (a : X ⟶ X)
    (ha : a ≫ a = 𝟙 X) (f g : T ⟶ X ⨿ V)
    (h : f ≫ coprod.desc (𝟙 X) (i ≫ a) = g ≫ coprod.desc (𝟙 X) i) :
    ∃ l : T ⟶ X ⨿ V,
      l ≫ coprod.desc (𝟙 X) i = f ≫ coprod.desc (𝟙 X) i ∧
      l ≫ coprod.desc (𝟙 X) (i ≫ a) = g ≫ coprod.desc (𝟙 X) (i ≫ a) := by
  refine exists_lift_of_coprod_cases f _ _ _ _ ?_ ?_
  · intro W j b hj
    refine ⟨j ≫ g, ?_, Category.assoc _ _ _⟩
    have h' := comp_comp_eq_of_comp_eq h (𝟙 W) j hj (Category.id_comp _)
    simp only [← Category.assoc, hj]
    simpa only [Category.assoc, coprod.inl_desc, Category.comp_id, Category.id_comp]
      using h'.symm
  · intro W j b hj
    refine exists_lift_of_coprod_cases (j ≫ g) _ _ _ _ ?_ ?_
    · intro Z k c hk
      refine ⟨k ≫ b ≫ coprod.inr, ?_, ?_⟩
      · simp only [← Category.assoc, hj]
      · simp only [← Category.assoc, hk]
        simpa only [Category.assoc, coprod.inl_desc, coprod.inr_desc, Category.comp_id]
          using comp_comp_eq_of_comp_eq h k j hj hk
    · intro Z k c hk
      refine ⟨k ≫ b ≫ i ≫ coprod.inl, ?_, ?_⟩
      · simp only [← Category.assoc, hj]
        simp only [Category.assoc, coprod.inr_desc, coprod.inl_desc, Category.comp_id]
      · have h' : (k ≫ b ≫ i) ≫ a = c ≫ i := by
          simpa only [Category.assoc, coprod.inl_desc, coprod.inr_desc, Category.comp_id]
            using comp_comp_eq_of_comp_eq h k j hj hk
        have hh := congrArg (fun z => z ≫ a) h'
        simp only [← Category.assoc, hk]
        simpa only [Category.assoc, ha, coprod.inl_desc, coprod.inr_desc,
          Category.comp_id] using hh

/-- **The diagonal together with the graph of a free involution on a subobject is an
equivalence relation.** The involution `a` is assumed to preserve `V`, in the form of an
endomorphism `b : V ⟶ V` with `b ≫ i = i ≫ a`, and to act freely on it. -/
theorem isEquivalenceRelation_coprod_desc_of_free_involution {X V : C} (i : V ⟶ X) [Mono i]
    (a : X ⟶ X) (ha : a ≫ a = 𝟙 X) (b : V ⟶ V) (hb : b ≫ i = i ≫ a)
    (hfree : ∀ {T : C} (c : T ⟶ V), c ≫ i = c ≫ i ≫ a → Subsingleton (T ⟶ X ⨿ V)) :
    IsEquivalenceRelation (coprod.desc (𝟙 X) i) (coprod.desc (𝟙 X) (i ≫ a)) := by
  let t := coprod.desc (𝟙 X) i
  let s := coprod.desc (𝟙 X) (i ≫ a)
  obtain ⟨c, hc₁, hc₂⟩ := exists_lift_coprod_desc_of_involution i a ha
    (pullback.fst s t) (pullback.snd s t) pullback.condition
  refine EquivalenceRelation.isEquivalenceRelation ?_
  exact {
    toJointlyMono₂ := jointlyMono₂_coprod_desc_of_free_involution i a hfree
    r := coprod.inl
    reflexivity₁ := coprod.inl_desc _ _
    reflexivity₂ := coprod.inl_desc _ _
    s := coprod.map (𝟙 X) b
    symmetry₁ := by
      refine coprod.hom_ext ?_ ?_
      · simp only [coprod.inl_map_assoc, coprod.inl_desc, Category.id_comp]
      · simp only [coprod.inr_map_assoc, coprod.inr_desc]
        exact hb
    symmetry₂ := by
      refine coprod.hom_ext ?_ ?_
      · simp only [coprod.inl_map_assoc, coprod.inl_desc, Category.id_comp]
      · simp only [coprod.inr_map_assoc, coprod.inr_desc]
        rw [← Category.assoc, hb, Category.assoc, ha, Category.comp_id]
    c := pullback.cone s t
    isLimit := pullback.isLimit s t
    t := c
    transitivity₁ := hc₁
    transitivity₂ := hc₂ }

end CategoryTheory

end
