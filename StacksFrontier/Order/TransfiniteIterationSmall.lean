module

public import Mathlib.Basic.Countable.Small
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Transfinite iteration of predicates and smallness

Constructions in the style of the reflection arguments of Stacks, Sets, Sections 3.9 and 3.11
build a set as the union of an increasing transfinite sequence of sets, each obtained from the
previous ones by a step function. This file records the facts about `transfiniteIterate` that
such constructions use: smallness is preserved, a limit stage is the union of the earlier ones,
and below an ordinal of large cofinality a small family of ordinals is bounded.

## Main results

* `small_transfiniteIterate`: iterating a step function that preserves `w`-small predicates
  gives `w`-small predicates at every ordinal of `Ordinal.{w}`.
* `transfiniteIterate_apply_iff_of_isSuccLimit`: at a limit stage a predicate holds iff it holds
  at an earlier stage.
* `Ordinal.exists_lt_forall_le_of_mk_lt_cof`: a family of fewer than `cof β` ordinals below `β`
  is bounded below `β`.
-/

@[expose] public section

open Cardinal

universe w

/-- A transfinite iteration of a step function preserving `w`-small predicates, starting from a
`w`-small predicate, is `w`-small at every ordinal of `Ordinal.{w}`. -/
public theorem small_transfiniteIterate {α : Type*} (φ : (α → Prop) → (α → Prop))
    (hφ : ∀ p : α → Prop, Small.{w} (Subtype p) → Small.{w} (Subtype (φ p)))
    (p : α → Prop) (hp : Small.{w} (Subtype p)) (b : Ordinal.{w}) :
    Small.{w} (Subtype (transfiniteIterate φ b p)) := by
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    rwa [transfiniteIterate_bot]
  | succ b hb ih =>
    rw [transfiniteIterate_succ _ _ _ hb]
    exact hφ _ ih
  | isSuccLimit b hb ih =>
    rw [transfiniteIterate_limit _ _ _ hb]
    have (c : Set.Iio b) : Small.{w} (Subtype (transfiniteIterate φ c.1 p)) := ih c.1 c.2
    refine small_of_surjective
      (f := fun x : Σ c : Set.Iio b, Subtype (transfiniteIterate φ c.1 p) =>
        ⟨x.2.1, by simp only [iSup_apply, iSup_Prop_eq]; exact ⟨x.1, x.2.2⟩⟩) ?_
    rintro ⟨a, ha⟩
    simp only [iSup_apply, iSup_Prop_eq] at ha
    obtain ⟨c, hc⟩ := ha
    exact ⟨⟨c, a, hc⟩, rfl⟩

/-- A predicate holds at a successor-limit stage of a transfinite iteration precisely when it
holds at some earlier stage. -/
public theorem transfiniteIterate_apply_iff_of_isSuccLimit {α : Type*}
    (φ : (α → Prop) → (α → Prop)) (p : α → Prop) {b : Ordinal.{w}}
    (hb : Order.IsSuccLimit b) (a : α) :
    transfiniteIterate φ b p a ↔ ∃ c < b, transfiniteIterate φ c p a := by
  rw [transfiniteIterate_limit _ _ _ hb]
  simp only [iSup_apply, iSup_Prop_eq, Subtype.exists, Set.mem_Iio, exists_prop]

/-- A family of ordinals below `β` indexed by a `w`-small type of cardinality less than the
cofinality of `β` is bounded by an ordinal below `β`. -/
public theorem Ordinal.exists_lt_forall_le_of_mk_lt_cof {β : Ordinal.{w}} {ι : Type*}
    [Small.{w} ι] (hι : #(Shrink.{w} ι) < β.cof) (o : ι → Ordinal.{w}) (ho : ∀ i, o i < β) :
    ∃ m < β, ∀ i, o i ≤ m := by
  refine ⟨⨆ k : Shrink.{w} ι, o ((equivShrink.{w} ι).symm k),
    Ordinal.iSup_lt_of_lt_cof hι (fun _ => ho _), fun i => ?_⟩
  have h := le_ciSup (f := fun k : Shrink.{w} ι => o ((equivShrink.{w} ι).symm k))
    Ordinal.bddAbove_of_small (equivShrink.{w} ι i)
  rwa [Equiv.symm_apply_apply] at h

/-- For an ordinal `β` of uncountable cofinality, every countable family of ordinals below `β`
is bounded by an ordinal below `β`. -/
public theorem Ordinal.exists_lt_forall_le_of_aleph0_lt_cof {β : Ordinal.{w}}
    (hβ : ℵ₀ < β.cof) {ι : Type*} [Countable ι] (o : ι → Ordinal.{w}) (ho : ∀ i, o i < β) :
    ∃ m < β, ∀ i, o i ≤ m := by
  have : Countable (Shrink.{w} ι) := Countable.of_equiv _ (equivShrink.{w} ι)
  exact Ordinal.exists_lt_forall_le_of_mk_lt_cof (mk_le_aleph0.trans_lt hβ) o ho
