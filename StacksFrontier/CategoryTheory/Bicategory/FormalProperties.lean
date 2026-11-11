module

public import StacksFrontier.CategoryTheory.Bicategory.InterchangeLaw

/-! # Formal properties of vertical and horizontal composition

Stacks Lemma 003F: vertical composition `≫` (Stacks' `∘`, written in diagram order) and
horizontal composition `◫` (Stacks' `⋆`, with `t ◫ s` the Stacks `s ⋆ t`) of natural
transformations are associative, the identity transformations `𝟙 F` are units for `≫`, the
identity transformations `𝟙 (𝟭 A)` of identity functors are units for `◫` and `≫`, and the
interchange law holds.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory

namespace CategoryTheory.NatTrans

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

/-- Horizontal composition `◫` of natural transformations is associative. -/
theorem hcomp_assoc {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : C ⥤ D}
    (t : F ⟶ F') (s : G ⟶ G') (r : H ⟶ H') :
    (t ◫ s) ◫ r = t ◫ (s ◫ r) := by
  ext X
  simp [Category.assoc]

/-- The identity transformation `𝟙 (𝟭 A)` of the identity functor is a left unit for
horizontal composition `◫`. -/
theorem id_id_hcomp {F F' : A ⥤ B} (t : F ⟶ F') : 𝟙 (𝟭 A) ◫ t = t := by
  ext X
  simp

/-- The identity transformation `𝟙 (𝟭 B)` of the identity functor is a right unit for
horizontal composition `◫`. -/
theorem hcomp_id_id {F F' : A ⥤ B} (t : F ⟶ F') : t ◫ 𝟙 (𝟭 B) = t := by
  ext X
  simp

/-- **Stacks 003F** (formal properties of vertical and horizontal composition). For natural
transformations between functors of arbitrary categories:
1. vertical composition `≫` and horizontal composition `◫` are associative;
2. the identity transformations `𝟙 F` are units for `≫`;
3. the identity transformations `𝟙 (𝟭 A)` of identity functors are units for `◫` and `≫`;
4. the interchange law `(t ≫ t') ◫ (s ≫ s') = (t ◫ s) ≫ (t' ◫ s')` holds.

Here `≫` is the Stacks `∘` in diagram order and `t ◫ s` is the Stacks `s ⋆ t`. -/
@[stacks 003F]
theorem vcomp_hcomp_formal_properties :
    -- (1) associativity of `≫`
    (∀ {F G H K : A ⥤ B} (a : F ⟶ G) (b : G ⟶ H) (c : H ⟶ K),
      (a ≫ b) ≫ c = a ≫ b ≫ c) ∧
    -- (1) associativity of `◫`
    (∀ {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : C ⥤ D}
      (t : F ⟶ F') (s : G ⟶ G') (r : H ⟶ H'), (t ◫ s) ◫ r = t ◫ (s ◫ r)) ∧
    -- (2) `𝟙 F` is a unit for `≫`
    (∀ {F G : A ⥤ B} (t : F ⟶ G), 𝟙 F ≫ t = t ∧ t ≫ 𝟙 G = t) ∧
    -- (3) `𝟙 (𝟭 A)` is a unit for `◫`
    (∀ {F F' : A ⥤ B} (t : F ⟶ F'), 𝟙 (𝟭 A) ◫ t = t ∧ t ◫ 𝟙 (𝟭 B) = t) ∧
    -- (3) `𝟙 (𝟭 A)` is a unit for `≫`
    (∀ {G : A ⥤ A} (u : 𝟭 A ⟶ G) (w : G ⟶ 𝟭 A), 𝟙 (𝟭 A) ≫ u = u ∧ w ≫ 𝟙 (𝟭 A) = w) ∧
    -- (4) the interchange law
    (∀ {F F' F'' : A ⥤ B} {G G' G'' : B ⥤ C}
      (t : F ⟶ F') (t' : F' ⟶ F'') (s : G ⟶ G') (s' : G' ⟶ G''),
      (t ≫ t') ◫ (s ≫ s') = (t ◫ s) ≫ (t' ◫ s')) :=
  ⟨fun a b c => Category.assoc a b c, fun t s r => hcomp_assoc t s r,
    fun t => ⟨Category.id_comp t, Category.comp_id t⟩,
    fun t => ⟨id_id_hcomp t, hcomp_id_id t⟩,
    fun u w => ⟨Category.id_comp u, Category.comp_id w⟩,
    fun t t' s s' => horiz_vert_interchange t t' s s'⟩

end CategoryTheory.NatTrans
