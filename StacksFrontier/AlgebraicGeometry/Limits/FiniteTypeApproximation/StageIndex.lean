module

public import Mathlib.Order.Directed
public import Mathlib.Order.Hom.Basic

/-!
# The index preorder of a two-stage approximation

Absolute Noetherian approximation builds its approximating inverse system in two stages: an
outer directed preorder `I`, and for each `i : I` an inner directed preorder `P i` of finite-type
models over the `i`-th stage.  The index preorder of the resulting system is the disjoint union
`Σ i, P i`, ordered by `⟨i, p⟩ ≤ ⟨i', p'⟩` exactly when `i ≤ i'` and the `i`-th model `p` is
carried into the `i'`-th model `p'` by the transition from `i` to `i'`.

The carrying relation is axiomatized here as `StageRel`: it is reflexive and transitive, it is
antitone in its first model and monotone in its second, and every model has a carrier at every
later outer index.  Those are the properties the construction actually produces, and they are
exactly what makes `Σ i, P i` a nonempty directed preorder whose projection to `I` has cofinal
image.

## Main definitions

* `Order.StageRel`: the axioms of a carrying relation between the inner preorders.
* `Order.StageIndex`: the disjoint union `Σ i, P i`, with its preorder.
* `Order.stageIndexProj`: the projection `StageIndex → I`, as an order homomorphism.
* `Order.ExactStageRel`, `Order.ExactStageIndex`, `Order.exactStageIndexProj`: the same, for a
  carrying relation that prescribes the carried model instead of bounding it, and which is
  therefore not monotone in that model.

## Main results

* `Order.StageRel.isDirected`: `StageIndex` is directed.
* `Order.StageRel.exists_stageIndexProj_ge`: the projection to `I` has cofinal image.
* `Order.ExactStageRel.isDirected` and `Order.ExactStageRel.exists_exactStageIndexProj_ge`: the
  same two conclusions from the common-carrier axiom.

## Implementation notes

The carrying relation takes the proof of `i ≤ i'` as an argument so that it can be read off a
family of transition maps indexed by that proof; since it is a proposition the choice of proof is
irrelevant, which is why no coherence axiom for it is needed.  The preorder on `Σ i, P i` is
defined directly rather than as a lexicographic or product order: the second component is
compared through the carrying relation, not through any order of its own.

`StageRel` assumes the relation is antitone in its first model and monotone in its second, and
uses that only to make `StageIndex` directed: two models are pushed up to a common outer index
and then replaced by an upper bound there.  A relation that *prescribes* the carried model —
"the image of this model is exactly that one" — has no such monotonicity, because enlarging the
carrier changes the prescribed datum.  `ExactStageRel` is the axiomatization such a relation
does satisfy: monotonicity is dropped and the existence of carriers is strengthened to the
existence of a *common* carrier for two models, which is what directedness needs.  No order on
the inner families is used.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

universe u v

namespace Order

variable {I : Type u} [Preorder I] {P : I → Type v} [∀ i, Preorder (P i)]

/-- The axioms of a carrying relation between the inner preorders of a two-stage approximation:
`rel h p q` says that the transition from `i` to `i'` carries the model `p` over `i` into the
model `q` over `i'`.

The relation is reflexive and transitive, antitone in the first model and monotone in the second,
and every model has a carrier at every later outer index. -/
structure StageRel (rel : ∀ {i i' : I}, i ≤ i' → P i → P i' → Prop) : Prop where
  /-- Every model is carried into itself. -/
  refl : ∀ {i : I} (p : P i), rel le_rfl p p
  /-- Carrying composes. -/
  trans : ∀ {i i' i'' : I} {h : i ≤ i'} {h' : i' ≤ i''} {p : P i} {q : P i'} {r : P i''},
    rel h p q → rel h' q r → rel (h.trans h') p r
  /-- A smaller model is carried into a larger one. -/
  mono : ∀ {i i' : I} {h : i ≤ i'} {p p' : P i} {q q' : P i'}, p' ≤ p → q ≤ q' →
    rel h p q → rel h p' q'
  /-- Every model has a carrier at every later outer index. -/
  exists_carrier : ∀ {i i' : I} (h : i ≤ i') (p : P i), ∃ q : P i', rel h p q

namespace StageRel

variable {rel : ∀ {i i' : I}, i ≤ i' → P i → P i' → Prop}

/-- The index preorder of a two-stage approximation: the disjoint union of the inner preorders,
ordered by the outer order together with the carrying relation. -/
def _root_.Order.StageIndex (_h : StageRel (P := P) rel) := Σ i : I, P i

variable (h : StageRel (P := P) rel)

/-- `⟨i, p⟩ ≤ ⟨i', q⟩` in `StageIndex h` when `i ≤ i'` and the transition carries `p` into `q`. -/
instance : LE (StageIndex h) where
  le a b := ∃ hab : a.1 ≤ b.1, rel hab a.2 b.2

/-- `a ≤ b` in `StageIndex h` if and only if `a.1 ≤ b.1` and `rel` relates `a.2` to `b.2`. -/
lemma le_def {a b : StageIndex h} : a ≤ b ↔ ∃ hab : a.1 ≤ b.1, rel hab a.2 b.2 := Iff.rfl

/-- The order on `StageIndex h` is a preorder. -/
instance : Preorder (StageIndex h) where
  le_refl a := ⟨le_rfl, h.refl a.2⟩
  le_trans _ _ _ := fun ⟨hab, rab⟩ ⟨hbc, rbc⟩ ↦ ⟨hab.trans hbc, h.trans rab rbc⟩

/-- `StageIndex h` is nonempty when `I` and every `P i` are nonempty. -/
instance [Nonempty I] [∀ i, Nonempty (P i)] : Nonempty (StageIndex h) :=
  ⟨⟨Classical.arbitrary I, Classical.arbitrary _⟩⟩

/-- The projection of the index preorder to the outer one. -/
def _root_.Order.stageIndexProj : StageIndex h →o I where
  toFun a := a.1
  monotone' _ _ hab := hab.1

/-- `stageIndexProj h` sends `a` to its outer index `a.1`. -/
@[simp]
lemma stageIndexProj_apply (a : StageIndex h) : stageIndexProj h a = a.1 := rfl

/-- The index preorder of a two-stage approximation is directed when the outer preorder and
every inner preorder are directed. -/
instance isDirected [IsDirected I (· ≤ ·)] [∀ i, IsDirected (P i) (· ≤ ·)] :
    IsDirected (StageIndex h) (· ≤ ·) where
  directed a b := by
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    obtain ⟨q, hq⟩ := h.exists_carrier hak a.2
    obtain ⟨q', hq'⟩ := h.exists_carrier hbk b.2
    obtain ⟨r, hqr, hq'r⟩ := directed_of (· ≤ ·) q q'
    exact ⟨⟨k, r⟩, ⟨hak, h.mono le_rfl hqr hq⟩, ⟨hbk, h.mono le_rfl hq'r hq'⟩⟩

/-- The projection to the outer index preorder has cofinal image: the outer index `i` is
already attained by any model over `i`. -/
lemma exists_stageIndexProj_ge [∀ i, Nonempty (P i)] (i : I) :
    ∃ a : StageIndex h, i ≤ stageIndexProj h a :=
  ⟨⟨i, Classical.arbitrary _⟩, le_rfl⟩

end StageRel

section Exact

variable {I : Type u} [Preorder I] {P : I → Type v}

/-- The axioms of a carrying relation that **prescribes** the carried model rather than bounding
it: `rel h p q` says that the transition from `i` to `i'` carries the model `p` over `i` onto the
model `q` over `i'`.

The relation is reflexive and transitive, and any two models have a common carrier at a common
later outer index.  Monotonicity in the second model — which `Order.StageRel` assumes — is
unavailable, because enlarging the carrier changes the prescribed datum; the common-carrier
axiom takes over its only role, making the index preorder directed. -/
structure ExactStageRel (rel : ∀ {i i' : I}, i ≤ i' → P i → P i' → Prop) : Prop where
  /-- Every model is carried onto itself. -/
  refl : ∀ {i : I} (p : P i), rel le_rfl p p
  /-- Carrying composes. -/
  trans : ∀ {i i' i'' : I} {h : i ≤ i'} {h' : i' ≤ i''} {p : P i} {q : P i'} {r : P i''},
    rel h p q → rel h' q r → rel (h.trans h') p r
  /-- Any two models have a common carrier at a common later outer index. -/
  exists_common_carrier : ∀ {i i' : I} (p : P i) (q : P i'),
    ∃ (k : I) (h : i ≤ k) (h' : i' ≤ k) (r : P k), rel h p r ∧ rel h' q r

namespace ExactStageRel

variable {rel : ∀ {i i' : I}, i ≤ i' → P i → P i' → Prop}

/-- The index preorder of a two-stage approximation with an exact carrying relation: the
disjoint union of the inner families, ordered by the outer order together with the relation. -/
def _root_.Order.ExactStageIndex (_h : ExactStageRel (P := P) rel) := Σ i : I, P i

variable (h : ExactStageRel (P := P) rel)

/-- `⟨i, p⟩ ≤ ⟨i', q⟩` in `ExactStageIndex h` when `i ≤ i'` and the transition carries `p` onto
`q`. -/
instance : LE (ExactStageIndex h) where
  le a b := ∃ hab : a.1 ≤ b.1, rel hab a.2 b.2

/-- `a ≤ b` in `ExactStageIndex h` if and only if `a.1 ≤ b.1` and `rel` relates `a.2` to `b.2`. -/
lemma le_def {a b : ExactStageIndex h} : a ≤ b ↔ ∃ hab : a.1 ≤ b.1, rel hab a.2 b.2 := Iff.rfl

/-- The order on `ExactStageIndex h` is a preorder. -/
instance : Preorder (ExactStageIndex h) where
  le_refl a := ⟨le_rfl, h.refl a.2⟩
  le_trans _ _ _ := fun ⟨hab, rab⟩ ⟨hbc, rbc⟩ ↦ ⟨hab.trans hbc, h.trans rab rbc⟩

/-- `ExactStageIndex h` is nonempty when `I` and every `P i` are nonempty. -/
instance [Nonempty I] [∀ i, Nonempty (P i)] : Nonempty (ExactStageIndex h) :=
  ⟨⟨Classical.arbitrary I, Classical.arbitrary _⟩⟩

/-- The projection of the index preorder to the outer one. -/
def _root_.Order.exactStageIndexProj : ExactStageIndex h →o I where
  toFun a := a.1
  monotone' _ _ hab := hab.1

/-- `exactStageIndexProj h` sends `a` to its outer index `a.1`. -/
@[simp]
lemma exactStageIndexProj_apply (a : ExactStageIndex h) : exactStageIndexProj h a = a.1 := rfl

/-- The index preorder of a two-stage approximation with an exact carrying relation is
directed. -/
instance isDirected : IsDirected (ExactStageIndex h) (· ≤ ·) where
  directed a b := by
    obtain ⟨k, hak, hbk, r, hr, hr'⟩ := h.exists_common_carrier a.2 b.2
    exact ⟨⟨k, r⟩, ⟨hak, hr⟩, ⟨hbk, hr'⟩⟩

/-- The projection to the outer index preorder has cofinal image: the outer index `i` is already
attained by any model over `i`. -/
lemma exists_exactStageIndexProj_ge [∀ i, Nonempty (P i)] (i : I) :
    ∃ a : ExactStageIndex h, i ≤ exactStageIndexProj h a :=
  ⟨⟨i, Classical.arbitrary _⟩, le_rfl⟩

end ExactStageRel

end Exact

end Order

end
