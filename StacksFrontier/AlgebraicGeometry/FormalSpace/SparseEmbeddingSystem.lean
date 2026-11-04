module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Set.Countable
public import Mathlib.Basic.Countable.Basic

/-!
# An inverse system of nonempty sets with surjective maps and no compatible family

The index set is the countable subsets of a fixed type `α`, ordered by inclusion; over a
countable subset `s` sits the set of injections `s ↪ ℕ` whose range has infinite complement, and
the transition maps are restrictions. The transition maps are surjective, and for an uncountable
`α` there is no compatible family of elements; the free modules on these sets have vanishing
inverse limit as well.

## Main definitions

* `AlgebraicGeometry.FormalSpace.CountableSubset`: the countable subsets of a type.
* `AlgebraicGeometry.FormalSpace.SparseEmbedding`: the injections into `ℕ` with infinite
  complement, and `AlgebraicGeometry.FormalSpace.sparseRestrict` their restrictions.
* `AlgebraicGeometry.FormalSpace.sparseEmbeddingSystem`: the inverse system.

## Main results

* `AlgebraicGeometry.FormalSpace.sparseRestrict_surjective`: the transition maps are surjective.
* `AlgebraicGeometry.FormalSpace.no_sparseEmbedding_sections`: there is no compatible family.
* `AlgebraicGeometry.FormalSpace.finsupp_sparseEmbedding_eq_zero`: the free modules on the system
  have vanishing inverse limit.

## References

* [Stacks Project, Tag 0ANX](https://stacks.math.columbia.edu/tag/0ANX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u v w

/-- A monotone `ℕ`-valued function on a preorder in which every countable family has an upper
bound attains its supremum. -/
theorem exists_max_of_countablyDirected {I : Type u} [Preorder I] (i₀ : I)
    (hI : ∀ f : ℕ → I, ∃ j, ∀ n, f n ≤ j) (f : I → ℕ) (hf : Monotone f) :
    ∃ i, ∀ j, f j ≤ f i := by
  have hb : BddAbove (Set.range f) := by
    by_contra hn
    have hex : ∀ n : ℕ, ∃ i, n < f i := by
      intro n
      by_contra! h
      exact hn ⟨n, by rintro m ⟨i, rfl⟩; exact h i⟩
    choose g hg using hex
    obtain ⟨j, hj⟩ := hI g
    exact not_lt_of_ge (hf (hj (f j))) (hg (f j))
  obtain ⟨i, hi⟩ := Nat.sSup_mem ⟨f i₀, Set.mem_range_self i₀⟩ hb
  exact ⟨i, fun j => hi ▸ le_csSup hb (Set.mem_range_self j)⟩

/-- Pushing a finitely supported function forward does not enlarge its support. -/
theorem mapDomain_support_card_le {α : Type u} {β : Type v}
    {M : Type w} [AddCommMonoid M] (f : α → β) (v : α →₀ M) :
    (Finsupp.mapDomain f v).support.card ≤ v.support.card := by
  classical
  exact (Finset.card_le_card Finsupp.mapDomain_support).trans Finset.card_image_le

/-- If pushing a finitely supported function forward does not shrink its support, the new
support is the image of the old one. -/
theorem mapDomain_support_eq_of_card_le {α : Type u} {β : Type v}
    [DecidableEq β] {M : Type w} [AddCommMonoid M] (f : α → β) (v : α →₀ M)
    (h : v.support.card ≤ (Finsupp.mapDomain f v).support.card) :
    (Finsupp.mapDomain f v).support = v.support.image f :=
  Finset.eq_of_subset_of_card_le Finsupp.mapDomain_support (Finset.card_image_le.trans h)

/-- Every countable family of countable subsets has an upper bound among the countable
subsets. -/
theorem countableSet_countablyDirected (α : Type u) :
    ∀ f : ℕ → {s : Set α // s.Countable}, ∃ j, ∀ n, f n ≤ j := fun f =>
  ⟨⟨⋃ n, (f n).val, Set.countable_iUnion fun n => (f n).property⟩,
    fun n => Set.subset_iUnion (fun n => (f n).val) n⟩

/-- The countable subsets of `α`, ordered by inclusion. -/
abbrev CountableSubset (α : Type u) := {s : Set α // s.Countable}

/-- A countable subset is a countable type. -/
instance countableSubtype {α : Type u} (s : CountableSubset α) : Countable s.val :=
  s.property.to_subtype

/-- The injections of a countable set into `ℕ` whose range has infinite complement. -/
abbrev SparseEmbedding {α : Type u} (s : CountableSubset α) :=
  {e : s.val ↪ ℕ // (Set.range e)ᶜ.Infinite}

/-- Restriction of an injection with infinite complement along an inclusion of countable
subsets. -/
def sparseRestrict {α : Type u} {s t : CountableSubset α} (h : s ≤ t)
    (e : SparseEmbedding t) : SparseEmbedding s :=
  ⟨⟨fun a => e.val ⟨a.val, h a.property⟩,
      fun _ _ hab => Subtype.ext (congrArg (fun a : t.val => a.val) (e.val.injective hab))⟩,
    e.property.mono (by
      rintro n hn ⟨a, ha⟩
      exact hn ⟨⟨a.val, h a.property⟩, ha⟩)⟩

/-- Every countable subset has an injection into `ℕ` with infinite complement. -/
theorem sparseEmbedding_nonempty {α : Type u} (s : CountableSubset α) :
    Nonempty (SparseEmbedding s) := by
  obtain ⟨e⟩ := nonempty_embedding_nat s.val
  let f : s.val ↪ ℕ := ⟨fun a => 2 * e a, by
    intro a b h
    apply e.injective
    dsimp at h
    omega⟩
  refine ⟨⟨f, ?_⟩⟩
  apply (Set.infinite_range_of_injective (f := fun n : ℕ => 2 * n + 1)
    (fun a b h => by dsimp at h; omega)).mono
  rintro n ⟨m, rfl⟩ ⟨a, ha⟩
  change 2 * e a = 2 * m + 1 at ha
  omega

/-- Restriction of injections with infinite complement along an inclusion of countable subsets
is surjective. -/
theorem sparseRestrict_surjective {α : Type u} {s t : CountableSubset α}
    (h : s ≤ t) : Function.Surjective (sparseRestrict h) := by
  classical
  intro e
  let c : ℕ ↪ ↥((Set.range e.val)ᶜ) := e.property.natEmbedding
  let U := {a : t.val // a.val ∉ s.val}
  let g : U ↪ ℕ := Classical.choice (nonempty_embedding_nat U)
  let f (a : t.val) : ℕ := if ha : a.val ∈ s.val then e.val ⟨a.val, ha⟩
    else (c (2 * g ⟨a, ha⟩)).val
  have hf : Function.Injective f := by
    intro a b hab
    have cross (a b : t.val) (ha : a.val ∈ s.val) (hb : b.val ∉ s.val) : f a ≠ f b := by
      simp only [f, dite_eq_left ha, dite_eq_right hb]
      exact fun hab => (c (2 * g ⟨b, hb⟩)).property ⟨⟨a.val, ha⟩, hab⟩
    by_cases ha : a.val ∈ s.val <;> by_cases hb : b.val ∈ s.val
    · simp only [f, dite_eq_left ha, dite_eq_left hb] at hab
      exact Subtype.ext (congrArg (fun a : s.val => a.val) (e.val.injective hab))
    · exact (cross a b ha hb hab).elim
    · exact (cross b a hb ha hab.symm).elim
    · simp only [f, dite_eq_right ha, dite_eq_right hb] at hab
      have he := c.injective (Subtype.ext hab)
      have hg : g ⟨a, ha⟩ = g ⟨b, hb⟩ := by omega
      exact congrArg Subtype.val (g.injective hg)
  let q (n : ℕ) : ℕ := (c (2 * n + 1)).val
  have hq : Function.Injective q := by
    intro a b hab
    have hc := c.injective (Subtype.ext hab)
    omega
  have h_inf : (Set.range f)ᶜ.Infinite := by
    apply (Set.infinite_range_of_injective hq).mono
    rintro n ⟨m, rfl⟩ ⟨a, ha⟩
    by_cases hs : a.val ∈ s.val
    · simp only [f, dite_eq_left hs] at ha
      exact (c (2 * m + 1)).property ⟨⟨a.val, hs⟩, ha⟩
    · simp only [f, dite_eq_right hs] at ha
      have hc := c.injective (Subtype.ext ha)
      omega
  refine ⟨⟨⟨f, hf⟩, h_inf⟩, Subtype.ext ?_⟩
  ext a
  simp [f, sparseRestrict]

/-- The inverse system over the countable subsets of `α` whose value at a countable subset is the
set of its injections into `ℕ` with infinite complement, with restrictions as transition maps. -/
def sparseEmbeddingSystem (α : Type u) :
    (CountableSubset α)ᵒᵖ ⥤ Type u where
  obj s := SparseEmbedding s.unop
  map f := ↾fun e => sparseRestrict (leOfHom f.unop) e
  map_id s := by
    ext e a
    rfl
  map_comp f g := by
    ext e a
    rfl

/-- There is no compatible family of injections with infinite complement over all countable
subsets of an uncountable set. -/
theorem no_sparseEmbedding_sections {α : Type u} [Uncountable α]
    (p : ∀ s : CountableSubset α, SparseEmbedding s)
    (hp : ∀ (s t : CountableSubset α) (h : s ≤ t), sparseRestrict h (p t) = p s) :
    False := by
  let s (a : α) : CountableSubset α := ⟨{a}, Set.countable_singleton a⟩
  let f (a : α) : ℕ := (p (s a)).val ⟨a, Set.mem_singleton a⟩
  have hpair (a b : α) (hab : f a = f b) : a = b := by
    let t : CountableSubset α := ⟨{a, b}, (Set.toFinite _).countable⟩
    have key (x : α) (hx : x ∈ t.val) : (p t).val ⟨x, hx⟩ = f x :=
      congrArg (fun q : SparseEmbedding (s x) => q.val ⟨x, by simp [s]⟩)
        (hp (s x) t fun y hy => by simp_all [s])
    exact congrArg Subtype.val ((p t).val.injective
      ((key a (by simp [t])).trans (hab.trans (key b (by simp [t])).symm)))
  exact not_countable (α := α) (Function.Injective.countable hpair)

/-- Restricting twice is restricting along the composite inclusion. -/
theorem sparseRestrict_comp {α : Type u} {s t r : CountableSubset α}
    (h : s ≤ t) (k : t ≤ r) (e : SparseEmbedding r) :
    sparseRestrict h (sparseRestrict k e) = sparseRestrict (h.trans k) e := rfl

/-- There is no compatible family of sparse embeddings indexed by the countable subsets lying
above a fixed countable subset of an uncountable set. -/
theorem no_sparseEmbedding_sections_of_le {α : Type u} [Uncountable α] (i : CountableSubset α)
    (p : ∀ s : CountableSubset α, i ≤ s → SparseEmbedding s)
    (hp : ∀ (s t : CountableSubset α) (hs : i ≤ s) (ht : i ≤ t) (h : s ≤ t),
      sparseRestrict h (p t ht) = p s hs) : False := by
  let j (s : CountableSubset α) : CountableSubset α :=
    ⟨s.val ∪ i.val, s.property.union i.property⟩
  have hj (s : CountableSubset α) : i ≤ j s := Set.subset_union_right
  have hs (s : CountableSubset α) : s ≤ j s := Set.subset_union_left
  let q (s : CountableSubset α) := sparseRestrict (hs s) (p (j s) (hj s))
  refine (no_sparseEmbedding_sections q fun s t h => ?_).elim
  change sparseRestrict h (sparseRestrict (hs t) (p (j t) (hj t))) =
    sparseRestrict (hs s) (p (j s) (hj s))
  rw [← hp (j s) (j t) (hj s) (hj t) (Set.union_subset_union_left _ h),
    sparseRestrict_comp, sparseRestrict_comp]

/-- The limit of the system of free modules on the sets `SparseEmbedding s` vanishes: for an
uncountable `α`, every compatible family of finitely supported functions is zero. -/
theorem finsupp_sparseEmbedding_eq_zero {α : Type u} [Uncountable α]
    {M : Type v} [AddCommMonoid M]
    (v : ∀ s : CountableSubset α, SparseEmbedding s →₀ M)
    (hv : ∀ (s t : CountableSubset α) (h : s ≤ t),
      Finsupp.mapDomain (sparseRestrict h) (v t) = v s) :
    ∀ s, v s = 0 := by
  classical
  have hmono : Monotone (fun s => (v s).support.card) := by
    intro s t h
    change (v s).support.card ≤ (v t).support.card
    rw [← hv s t h]
    exact mapDomain_support_card_le _ _
  obtain ⟨i, hi⟩ := exists_max_of_countablyDirected
    (⟨∅, Set.countable_empty⟩ : CountableSubset α)
    (countableSet_countablyDirected α) (fun s => (v s).support.card) hmono
  rcases (v i).support.eq_empty_or_nonempty with hzero | ⟨e, he⟩
  · exact fun s => Finsupp.support_eq_empty.mp
      (Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (by simpa [hzero] using hi s)))
  have h_image (s t : CountableSubset α) (hs : i ≤ s) (h : s ≤ t) :
      (v s).support = (v t).support.image (sparseRestrict h) := by
    rw [← hv s t h]
    exact mapDomain_support_eq_of_card_le _ _ (by rw [hv s t h]; exact (hi t).trans (hmono hs))
  have h_inj (s : CountableSubset α) (hs : i ≤ s) :
      Set.InjOn (sparseRestrict hs) (v s).support :=
    Finset.card_image_iff.mp (by rw [← h_image i s le_rfl hs]; exact le_antisymm (hmono hs) (hi s))
  have hex (s : CountableSubset α) (hs : i ≤ s) :
      ∃ e' ∈ (v s).support, sparseRestrict hs e' = e :=
    Finset.mem_image.mp (by rwa [← h_image i s le_rfl hs])
  choose p hp_mem hp using hex
  have hp_compat (s t : CountableSubset α) (hs : i ≤ s) (ht : i ≤ t) (h : s ≤ t) :
      sparseRestrict h (p t ht) = p s hs := by
    refine h_inj s hs ?_ (hp_mem s hs) ?_
    · rw [h_image s t hs h]
      exact Finset.mem_image.mpr ⟨p t ht, hp_mem t ht, rfl⟩
    · rw [sparseRestrict_comp, hp, hp]
  exact (no_sparseEmbedding_sections_of_le i p hp_compat).elim

end AlgebraicGeometry.FormalSpace

end
