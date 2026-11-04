module

public import StacksFrontier.CategoryTheory.BifunctorProdMap

/-!
# Associativity constraints along a comparison of bifunctors

Let `L : C ⥤ D` be a functor, `A` and `B` bifunctors on `C` and `D`, and
`α : A ⋙ L ⟶ L.prod L ⋙ B` a comparison of bifunctors.  Given associativity constraints `aA` of
`A` and `aB` of `B`, the comparison is *compatible* with them when `L` carries `aA` to `aB`
through `α` — the associativity law of a monoidal functor.  This is the condition the
associativity of the abstract relative cup product
(`Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_assoc`, Tag 0FP4) consumes.

This file proves two facts about that condition.

* **Transport.**  If `L` is fully faithful and `α` is an isomorphism, an associativity constraint
  `aB` of `B` determines a unique constraint of `A` with which `α` is compatible:
  `CategoryTheory.transportedAssociator`.  It is natural as soon as `aB` is.  This is how a
  monoidal structure is carried along an equivalence, and it is what the source does when it
  identifies `D(A)` with the derived category of modules on the one-point ringed space
  `({*}, A)`.
* **Composition.**  Compatibility is stable under composition of comparisons:
  `CategoryTheory.ComparisonAssociative.comp`.

## Main definitions

* `CategoryTheory.ComparisonAssociative` — the compatibility of a comparison of bifunctors with
  two associativity constraints.
* `CategoryTheory.transportedAssociator` — the constraint carried back along a fully faithful
  functor and an invertible comparison.

## Main results

* `CategoryTheory.comparisonAssociative_transportedAssociator` — the comparison is compatible
  with the transported constraint.
* `CategoryTheory.transportedAssociator_naturality` — the transported constraint is natural.
* `CategoryTheory.transportedAssociator_unique` — it is the only constraint with which the
  comparison is compatible.
* `CategoryTheory.ComparisonAssociative.comp` — compatibility of two comparisons gives
  compatibility of their composite.
-/

@[expose] public section

open scoped CategoryTheory.Prod

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

section Compatibility

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D}
  (A : C × C ⥤ C) (B : D × D ⥤ D)

/-- **A comparison of bifunctors is compatible with two associativity constraints** when `L`
carries the constraint `aA` of `A` to the constraint `aB` of `B` through the comparison `α`:
for all `X, Y, Z` the two maps `L((XY)Z) ⟶ LX(LY LZ)` agree.  This is the associativity law of a
monoidal functor, and it is the hypothesis `hα` of
`Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_assoc`. -/
def ComparisonAssociative (α : A ⋙ L ⟶ L.prod L ⋙ B)
    (aA : ∀ X Y Z : C, A.obj (A.obj (X, Y), Z) ⟶ A.obj (X, A.obj (Y, Z)))
    (aB : ∀ U V W : D, B.obj (B.obj (U, V), W) ⟶ B.obj (U, B.obj (V, W))) : Prop :=
  ∀ X Y Z : C,
    α.app (A.obj (X, Y), Z) ≫ B.map (α.app (X, Y) ×ₘ 𝟙 (L.obj Z)) ≫
        aB (L.obj X) (L.obj Y) (L.obj Z) =
      L.map (aA X Y Z) ≫ α.app (X, A.obj (Y, Z)) ≫ B.map (𝟙 (L.obj X) ×ₘ α.app (Y, Z))

end Compatibility

/-! ### Bookkeeping in one factor of a bifunctor -/

section Bookkeeping

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] (B : C₁ × C₂ ⥤ C₃)

/-- Two morphisms in the second factor, each paired with an identity, compose. -/
@[reassoc]
lemma bifunctor_map_id_prod_comp (X : C₁) {Y Y' Y'' : C₂} (f : Y ⟶ Y') (g : Y' ⟶ Y'') :
    B.map (𝟙 X ×ₘ f) ≫ B.map (𝟙 X ×ₘ g) = B.map (𝟙 X ×ₘ (f ≫ g)) := by
  rw [← B.map_comp, prod_comp, Category.id_comp]

/-- Two morphisms in the first factor, each paired with an identity, compose. -/
@[reassoc]
lemma bifunctor_map_prod_id_comp {X X' X'' : C₁} (f : X ⟶ X') (g : X' ⟶ X'') (Y : C₂) :
    B.map (f ×ₘ 𝟙 Y) ≫ B.map (g ×ₘ 𝟙 Y) = B.map ((f ≫ g) ×ₘ 𝟙 Y) := by
  rw [← B.map_comp, prod_comp, Category.id_comp]

/-- A bifunctor sends a pair of identities to an identity. -/
lemma bifunctor_map_id_prod_id (X : C₁) (Y : C₂) : B.map (𝟙 X ×ₘ 𝟙 Y) = 𝟙 (B.obj (X, Y)) :=
  B.map_id (X, Y)

end Bookkeeping

/-! ### Transport along a fully faithful functor -/

section Transport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D}
  (hL : L.FullyFaithful) (A : C × C ⥤ C) (B : D × D ⥤ D) (τ : A ⋙ L ≅ L.prod L ⋙ B)
  (aB : ∀ U V W : D, B.obj (B.obj (U, V), W) ⟶ B.obj (U, B.obj (V, W)))

/-- **The associativity constraint of `A` carried back from that of `B`** along a fully
faithful functor `L` and an invertible comparison `τ : A ⋙ L ≅ L.prod L ⋙ B`: the unique
preimage under `L` of
`L((XY)Z) ≅ L(XY) LZ ≅ (LX LY) LZ ⟶ LX (LY LZ) ≅ LX L(YZ) ≅ L(X(YZ))`. -/
def transportedAssociator (X Y Z : C) : A.obj (A.obj (X, Y), Z) ⟶ A.obj (X, A.obj (Y, Z)) :=
  hL.preimage (τ.hom.app (A.obj (X, Y), Z) ≫ B.map (τ.hom.app (X, Y) ×ₘ 𝟙 (L.obj Z)) ≫
    aB (L.obj X) (L.obj Y) (L.obj Z) ≫ B.map (𝟙 (L.obj X) ×ₘ τ.inv.app (Y, Z)) ≫
      τ.inv.app (X, A.obj (Y, Z)))

/-- `L` of the transported constraint is the composite it is the preimage of. -/
theorem map_transportedAssociator (X Y Z : C) :
    L.map (transportedAssociator hL A B τ aB X Y Z) =
      τ.hom.app (A.obj (X, Y), Z) ≫ B.map (τ.hom.app (X, Y) ×ₘ 𝟙 (L.obj Z)) ≫
        aB (L.obj X) (L.obj Y) (L.obj Z) ≫ B.map (𝟙 (L.obj X) ×ₘ τ.inv.app (Y, Z)) ≫
          τ.inv.app (X, A.obj (Y, Z)) :=
  hL.map_preimage _

/-- **The comparison is compatible with the transported constraint.** -/
theorem comparisonAssociative_transportedAssociator :
    ComparisonAssociative A B τ.hom (transportedAssociator hL A B τ aB) aB := by
  intro X Y Z
  rw [map_transportedAssociator]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [bifunctor_map_id_prod_comp, Iso.inv_hom_id_app, bifunctor_map_id_prod_id]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  rw [Category.comp_id]

/-- **The transported constraint is the only one with which the comparison is compatible.** -/
theorem transportedAssociator_unique
    (aA : ∀ X Y Z : C, A.obj (A.obj (X, Y), Z) ⟶ A.obj (X, A.obj (Y, Z)))
    (h : ComparisonAssociative A B τ.hom aA aB) (X Y Z : C) :
    aA X Y Z = transportedAssociator hL A B τ aB X Y Z := by
  apply hL.map_injective
  rw [map_transportedAssociator, reassoc_of% (h X Y Z), bifunctor_map_id_prod_comp_assoc,
    Iso.hom_inv_id_app, bifunctor_map_id_prod_id]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  rw [Category.id_comp, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [Category.comp_id]

/-- The comparison at a pair of morphisms, in the form `L(A(u, v)) = τ ≫ B(Lu, Lv) ≫ τ⁻¹`. -/
private lemma map_map_eq {X X' Y Y' : C} (u : X ⟶ X') (v : Y ⟶ Y') :
    L.map (A.map (u ×ₘ v)) =
      τ.hom.app (X, Y) ≫ B.map (L.map u ×ₘ L.map v) ≫ τ.inv.app (X', Y') := by
  calc L.map (A.map (u ×ₘ v)) =
        L.map (A.map (u ×ₘ v)) ≫ τ.hom.app (X', Y') ≫ τ.inv.app (X', Y') := by simp
    _ = _ := by rw [reassoc_of% (bifunctor_comparison_naturality A B τ.hom u v)]

/-- **The transported constraint is natural** as soon as the constraint of `B` is. -/
theorem transportedAssociator_naturality
    (haB : ∀ {U U' V V' W W' : D} (u : U ⟶ U') (v : V ⟶ V') (w : W ⟶ W'),
      B.map (B.map (u ×ₘ v) ×ₘ w) ≫ aB U' V' W' = aB U V W ≫ B.map (u ×ₘ B.map (v ×ₘ w)))
    {X X' Y Y' Z Z' : C} (u : X ⟶ X') (v : Y ⟶ Y') (w : Z ⟶ Z') :
    A.map (A.map (u ×ₘ v) ×ₘ w) ≫ transportedAssociator hL A B τ aB X' Y' Z' =
      transportedAssociator hL A B τ aB X Y Z ≫ A.map (u ×ₘ A.map (v ×ₘ w)) := by
  apply hL.map_injective
  rw [L.map_comp, L.map_comp, map_transportedAssociator, map_transportedAssociator,
    map_map_eq A B τ (A.map (u ×ₘ v)) w, map_map_eq A B τ u (A.map (v ×ₘ w)),
    map_map_eq A B τ u v, map_map_eq A B τ v w]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have e₁ : B.map ((τ.hom.app (X, Y) ≫ B.map (L.map u ×ₘ L.map v) ≫ τ.inv.app (X', Y')) ×ₘ
        L.map w) ≫ B.map (τ.hom.app (X', Y') ×ₘ 𝟙 (L.obj Z')) =
      B.map (τ.hom.app (X, Y) ×ₘ 𝟙 (L.obj Z)) ≫
        B.map (B.map (L.map u ×ₘ L.map v) ×ₘ L.map w) := by
    rw [← B.map_comp, ← B.map_comp]
    congr 1
    apply Prod.hom_ext <;> simp
  have e₂ : B.map (L.map u ×ₘ B.map (L.map v ×ₘ L.map w)) ≫
        B.map (𝟙 (L.obj X') ×ₘ τ.inv.app (Y', Z')) =
      B.map (𝟙 (L.obj X) ×ₘ τ.inv.app (Y, Z)) ≫
        B.map (L.map u ×ₘ (τ.hom.app (Y, Z) ≫ B.map (L.map v ×ₘ L.map w) ≫
          τ.inv.app (Y', Z'))) := by
    rw [← B.map_comp, ← B.map_comp]
    congr 1
    apply Prod.hom_ext <;> simp
  rw [reassoc_of% e₁, reassoc_of% (haB (L.map u) (L.map v) (L.map w)), reassoc_of% e₂]

end Transport

/-! ### Composition -/

section Composition

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {L₁ : C ⥤ D} {L₂ : D ⥤ E}
  {A : C × C ⥤ C} {B : D × D ⥤ D} {B' : E × E ⥤ E}
  {α : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ B} {β : B ⋙ L₂ ⟶ L₂.prod L₂ ⋙ B'}
  {aA : ∀ X Y Z : C, A.obj (A.obj (X, Y), Z) ⟶ A.obj (X, A.obj (Y, Z))}
  {aB : ∀ U V W : D, B.obj (B.obj (U, V), W) ⟶ B.obj (U, B.obj (V, W))}
  {aB' : ∀ U V W : E, B'.obj (B'.obj (U, V), W) ⟶ B'.obj (U, B'.obj (V, W))}

/-- **Compatibility with associativity constraints is stable under composition of
comparisons.**  If `α` is compatible with `aA` and `aB`, and `β` with `aB` and `aB'`, then the
composite comparison `L₂α ≫ β` for `L₁ ⋙ L₂` is compatible with `aA` and `aB'`. -/
theorem ComparisonAssociative.comp (hα : ComparisonAssociative A B α aA aB)
    (hβ : ComparisonAssociative B B' β aB aB') :
    ComparisonAssociative (L := L₁ ⋙ L₂) A B'
      (Functor.whiskerRight α L₂ ≫ Functor.whiskerLeft (L₁.prod L₁) β) aA aB' := by
  intro X Y Z
  have nat₁ := bifunctor_comparison_naturality B B' β (α.app (X, Y)) (𝟙 (L₁.obj Z))
  have nat₂ := bifunctor_comparison_naturality B B' β (𝟙 (L₁.obj X)) (α.app (Y, Z))
  rw [L₂.map_id] at nat₁ nat₂
  dsimp only [Functor.comp_obj, Functor.prod_obj] at nat₁ nat₂
  show (L₂.map (α.app (A.obj (X, Y), Z)) ≫ β.app (L₁.obj (A.obj (X, Y)), L₁.obj Z)) ≫
      B'.map ((L₂.map (α.app (X, Y)) ≫ β.app (L₁.obj X, L₁.obj Y)) ×ₘ
        𝟙 (L₂.obj (L₁.obj Z))) ≫ aB' (L₂.obj (L₁.obj X)) (L₂.obj (L₁.obj Y)) (L₂.obj (L₁.obj Z)) =
    L₂.map (L₁.map (aA X Y Z)) ≫ (L₂.map (α.app (X, A.obj (Y, Z))) ≫
      β.app (L₁.obj X, L₁.obj (A.obj (Y, Z)))) ≫
        B'.map (𝟙 (L₂.obj (L₁.obj X)) ×ₘ (L₂.map (α.app (Y, Z)) ≫ β.app (L₁.obj Y, L₁.obj Z)))
  rw [← bifunctor_map_prod_id_comp, ← bifunctor_map_id_prod_comp]
  simp only [Category.assoc]
  rw [reassoc_of% nat₁.symm]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  rw [hβ (L₁.obj X) (L₁.obj Y) (L₁.obj Z), ← L₂.map_comp_assoc,
    ← L₂.map_comp_assoc, Category.assoc, hα X Y Z]
  simp only [L₂.map_comp, Category.assoc]
  rw [reassoc_of% nat₂]

end Composition

end CategoryTheory
