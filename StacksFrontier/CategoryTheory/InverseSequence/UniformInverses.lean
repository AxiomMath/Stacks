module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.Order.Basic

/-!
# Uniform inverses of a morphism of inverse sequences

A morphism `α : X ⟶ Y` of inverse sequences `ℕᵒᵖ ⥤ C` *has uniform inverses* when a single shift
`c` works at every level: for each `n` there is a morphism `Y_{n+c} ⟶ X_n` whose two round trips
with `α` are the transition maps `X_{n+c} ⟶ X_n` and `Y_{n+c} ⟶ Y_n`.  This is the form in which
the isomorphisms of the strict pro-category of [Stacks, Tag 0GA5] are produced: compared with an
isomorphism of pro-objects, the later level is `n + c` with `c` independent of `n`.

## Main definitions

* `CategoryTheory.InverseSequence.HasUniformInverses`: the property.

## Main results

* `CategoryTheory.InverseSequence.hasUniformInverses_of_eventually`: it is enough to produce the
  inverses from the level `n + c` at the levels `n ≥ N`, for some `N`.
* `CategoryTheory.InverseSequence.HasUniformInverses.comp`,
  `CategoryTheory.InverseSequence.HasUniformInverses.of_isIso` and
  `CategoryTheory.InverseSequence.HasUniformInverses.whiskerRight`: stability under composition,
  for natural isomorphisms, and under any functor.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.InverseSequence

universe v u v' u'

variable {C : Type u} [Category.{v} C]

/-- The transition map `X_m ⟶ X_n` of an inverse sequence, for `n ≤ m`. -/
abbrev tr (X : ℕᵒᵖ ⥤ C) {n m : ℕ} (h : n ≤ m) : X.obj (op m) ⟶ X.obj (op n) :=
  X.map (homOfLE h).op

/-- Transition maps compose: `X_k ⟶ X_m ⟶ X_n` is the transition map `X_k ⟶ X_n`. -/
theorem tr_comp (X : ℕᵒᵖ ⥤ C) {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    tr X h' ≫ tr X h = tr X (h.trans h') := by
  rw [← X.map_comp]
  rfl

/-- A morphism of inverse sequences commutes with the transition maps. -/
@[reassoc]
theorem tr_naturality {X Y : ℕᵒᵖ ⥤ C} (α : X ⟶ Y) {n m : ℕ} (h : n ≤ m) :
    tr X h ≫ α.app (op n) = α.app (op m) ≫ tr Y h :=
  α.naturality _

/-- The transition map `X_m ⟶ X_n` does not depend on the proof of `n ≤ m`. -/
theorem tr_eq (X : ℕᵒᵖ ⥤ C) {n m : ℕ} (h h' : n ≤ m) : tr X h = tr X h' := rfl

/-- The transition map `X_n ⟶ X_n` is the identity. -/
theorem tr_refl (X : ℕᵒᵖ ⥤ C) (n : ℕ) : tr X (le_refl n) = 𝟙 _ := by
  rw [← X.map_id]
  rfl

/-- `α : X ⟶ Y` *has uniform inverses with shift `c`* if for all levels `n + c ≤ m` there is a
morphism `Y_m ⟶ X_n` whose two round trips with `α` are the transition maps. -/
def HasUniformInversesWith {X Y : ℕᵒᵖ ⥤ C} (α : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ n m : ℕ, n + c ≤ m → ∃ s : Y.obj (op m) ⟶ X.obj (op n),
    ∃ h : n ≤ m, α.app (op m) ≫ s = tr X h ∧ s ≫ α.app (op n) = tr Y h

/-- `α : X ⟶ Y` *has uniform inverses* if it has uniform inverses with some shift `c`. -/
def HasUniformInverses {X Y : ℕᵒᵖ ⥤ C} (α : X ⟶ Y) : Prop :=
  ∃ c : ℕ, HasUniformInversesWith α c

variable {X Y Z : ℕᵒᵖ ⥤ C}

/-- A uniform inverse for a shift `c` is one for every larger shift. -/
theorem HasUniformInversesWith.mono {α : X ⟶ Y} {c d : ℕ} (h : HasUniformInversesWith α c)
    (hcd : c ≤ d) : HasUniformInversesWith α d :=
  fun n m hm => h n m (by omega)

/-- Finitely many morphisms each having uniform inverses have them with a common shift. -/
theorem exists_hasUniformInversesWith_of_finite {X' Y' : ℤ → (ℕᵒᵖ ⥤ C)} (β : ∀ i, X' i ⟶ Y' i)
    (hβ : ∀ i, HasUniformInverses (β i)) (lo : ℤ) (L : ℕ) :
    ∃ c : ℕ, ∀ i : ℤ, lo ≤ i → i ≤ lo + L → HasUniformInversesWith (β i) c := by
  induction L with
  | zero =>
    obtain ⟨c, hc⟩ := hβ lo
    exact ⟨c, fun i h₁ h₂ => by
      obtain rfl : i = lo := by omega
      exact hc⟩
  | succ L ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := hβ (lo + (L + 1 : ℕ))
    refine ⟨max c d, fun i h₁ h₂ => ?_⟩
    by_cases hi : i ≤ lo + L
    · exact (hc i h₁ hi).mono (le_max_left _ _)
    · obtain rfl : i = lo + (L + 1 : ℕ) := by omega
      exact hd.mono (le_max_right _ _)

/-- Uniform inverses at the levels `n ≥ N`, from level `n + c`, give uniform inverses. -/
theorem hasUniformInverses_of_eventually (α : X ⟶ Y) (c N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → ∃ s : Y.obj (op (n + c)) ⟶ X.obj (op n),
      α.app (op (n + c)) ≫ s = tr X (Nat.le_add_right n c) ∧
        s ≫ α.app (op n) = tr Y (Nat.le_add_right n c)) :
    HasUniformInverses α := by
  refine ⟨N + c, fun n m hm => ?_⟩
  obtain ⟨s, hs₁, hs₂⟩ := h (n + N) (Nat.le_add_left N n)
  have hle : n + N + c ≤ m := by omega
  refine ⟨tr Y hle ≫ s ≫ tr X (Nat.le_add_right n N), by omega, ?_, ?_⟩
  · rw [← tr_naturality_assoc, reassoc_of% hs₁, tr_comp, tr_comp]
  · rw [Category.assoc, Category.assoc, tr_naturality, reassoc_of% hs₂, tr_comp, tr_comp]

/-- Uniform inverses compose. -/
theorem HasUniformInverses.comp {α : X ⟶ Y} {β : Y ⟶ Z} (hα : HasUniformInverses α)
    (hβ : HasUniformInverses β) : HasUniformInverses (α ≫ β) := by
  obtain ⟨c, hc⟩ := hα
  obtain ⟨d, hd⟩ := hβ
  refine ⟨c + d, fun n m hm => ?_⟩
  obtain ⟨s, hnm₁, hs₁, hs₂⟩ := hc n (n + c) le_rfl
  obtain ⟨t, hnm₂, ht₁, ht₂⟩ := hd (n + c) m (by omega)
  refine ⟨t ≫ s, by omega, ?_, ?_⟩
  · rw [NatTrans.comp_app, Category.assoc, reassoc_of% ht₁, ← tr_naturality_assoc, hs₁,
      tr_comp]
  · rw [NatTrans.comp_app, Category.assoc, reassoc_of% hs₂, tr_naturality, reassoc_of% ht₂,
      tr_comp]

/-- A natural isomorphism has uniform inverses, with shift `0`. -/
theorem HasUniformInverses.of_isIso (α : X ⟶ Y) [IsIso α] : HasUniformInverses α := by
  refine ⟨0, fun n m hm => ⟨inv (α.app (op m)) ≫ tr X (show n ≤ m by omega), by omega, ?_, ?_⟩⟩
  · rw [IsIso.hom_inv_id_assoc]
  · rw [Category.assoc, tr_naturality, IsIso.inv_hom_id_assoc]

/-- If `α` and `α ≫ p` have uniform inverses, so does `p`. -/
theorem HasUniformInverses.of_comp {W : ℕᵒᵖ ⥤ C} {α : W ⟶ X} {p : X ⟶ Y}
    (hα : HasUniformInverses α) (hαp : HasUniformInverses (α ≫ p)) :
    HasUniformInverses p := by
  obtain ⟨c, hc⟩ := hα
  obtain ⟨d, hd⟩ := hαp
  refine ⟨d + c, fun n m hm => ?_⟩
  obtain ⟨t, _h, ht₁, ht₂⟩ := hd n (n + d) le_rfl
  obtain ⟨s, hnm, hs₁, hs₂⟩ := hc (n + d) m (by omega)
  have ht₁' : α.app (op (n + d)) ≫ p.app (op (n + d)) ≫ t = tr W (Nat.le_add_right n d) := by
    rw [← Category.assoc, ← NatTrans.comp_app, ht₁]
  have ht₂' : t ≫ α.app (op n) ≫ p.app (op n) = tr Y (Nat.le_add_right n d) := by
    rw [← NatTrans.comp_app, ht₂]
  refine ⟨tr Y hnm ≫ t ≫ α.app (op n), by omega, ?_, ?_⟩
  · rw [← tr_naturality_assoc, ← hs₂, Category.assoc, reassoc_of% ht₁', tr_naturality,
      reassoc_of% hs₂, tr_comp]
  · rw [Category.assoc, Category.assoc, ht₂', tr_comp]

/-- Uniform inverses are preserved by any functor. -/
theorem HasUniformInverses.whiskerRight {D : Type u'} [Category.{v'} D] {α : X ⟶ Y}
    (hα : HasUniformInverses α) (F : C ⥤ D) :
    HasUniformInverses (Functor.whiskerRight α F) := by
  obtain ⟨c, hc⟩ := hα
  refine ⟨c, fun n m hm => ?_⟩
  obtain ⟨s, h, hs₁, hs₂⟩ := hc n m hm
  refine ⟨F.map s, h, ?_, ?_⟩ <;>
    simp only [Functor.whiskerRight_app, Functor.comp_map, ← F.map_comp, hs₁, hs₂]

end CategoryTheory.InverseSequence

end
