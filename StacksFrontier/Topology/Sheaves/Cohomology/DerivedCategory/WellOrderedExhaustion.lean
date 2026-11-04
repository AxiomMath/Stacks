module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Sets.Opens

/-!
# The well ordered exhaustion attached to a covering collection

[Stacks, Tag 0D6B] glues locally given derived objects along a *well ordered increasing* open
cover `X = ⋃_{α ∈ E} W_α`, one satisfying `W_β ⊆ W_α` for `β < α` and `W_α = ⋃_{β < α} W_β`
whenever `α` is not a successor.  The proof of [Stacks, Tag 0D6C] — glueing over an arbitrary
covering collection `ℬ` — begins by *producing* such a cover from `ℬ`: well order `ℬ` and take
`W_α` to be the union of the members preceding `α`.

This file carries that production, and nothing else.  It is pure order theory: the statements
hold in any complete lattice, so they apply to `TopologicalSpace.Opens X` for a ringed space `X`
with no reference to sheaves or derived categories.

## Main definitions

* `Stacks.DerivedGlueing.supBelow`: the supremum of the members of a family indexed by a linear
  order that strictly precede a given stage — the exhaustion `W_α = ⨆_{β < α} U_β`.
* `Stacks.DerivedGlueing.withTopExtend`: a family indexed by `ι`, read on `WithTop ι` by sending
  the adjoined top to `⊥`.  Adjoining a top is what makes the *last* stage of the exhaustion the
  union of the whole family.

## Main results

* `Stacks.DerivedGlueing.supBelow_monotone`, `supBelow_le_supBelow_of_lt`: the exhaustion is
  increasing, which is the hypothesis `hsucc` of
  `Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover` in its strongest form.
* `Stacks.DerivedGlueing.supBelow_eq_sup_of_isPred`: at a successor stage the exhaustion grows by
  exactly one member, `W_{α} = W_β ⊔ U_β` for `β` the immediate predecessor of `α`.  This is the
  step at which the source's recursion invokes the two-open case of [Stacks, Tag 0D6A].
* `Stacks.DerivedGlueing.supBelow_eq_iSup_supBelow_of_not_isPred`: at a stage that is not a
  successor the exhaustion is the union of the earlier stages — the hypothesis `hlimit` of
  `Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover`, satisfied *unconditionally* by the
  exhaustion.
* `Stacks.DerivedGlueing.exists_wellOrderedCover_of_sSup_eq_top`: **every** covering collection in
  a complete lattice is exhausted by a well ordered increasing family satisfying the limit
  condition, with every stage a union of members of the collection and every member contained in
  some stage.  This is the bridge from Situation 0D67's collection `ℬ` to [Stacks, Tag 0D6B]'s
  cover.
* `Stacks.DerivedGlueing.eq_sSup_range_of_not_isPred`: a stage of an increasing cover that is not
  a successor is the union of the stages it contains — the hypothesis that
  `Stacks.DerivedGlueing.HasUniqueSolutionOverIso` and `HasGluingForHomsOver` impose on the open
  they are read over, supplied at a limit stage.
* `Stacks.DerivedGlueing.eq_top_of_isGreatest`: **the degeneracy criterion.** If the index set of
  an increasing cover has a greatest element, the cover *displays* `⊤`.  See the section below.

## The degeneracy criterion, and why the index set must have no greatest element

A datum of [Stacks, Tag 0D6B] over an index set with a greatest element `g` has `W_g = ⊤`, by
`Stacks.DerivedGlueing.eq_top_of_isGreatest`.  The prescribed object `K_g` then already lives on
all of `X`, and the glueing problem is solved by `K_g` itself: there is nothing transfinite left.
Equivalently, the tag's content is concentrated entirely in index sets with **no** greatest
element — in particular in *infinite* chains, since a nonempty finite linear order has a greatest
element.

This matters for reading the tag rather than only for proving it.  A witness for the tag's datum
built on a chain of finite length is degenerate in exactly the sense of the covering-set rule: it
satisfies every binder and certifies nothing, because the conclusion is reached by taking the top
stage.  A non-degenerate witness needs a strictly increasing chain of *proper* opens whose union
is everything, hence an index set with no greatest element, hence a carrier on which such a chain
exists at all — never a noetherian one, where every increasing chain of opens stabilises.

`Stacks.DerivedGlueing.supBelow_singletons_nat`, `supBelow_singletons_nat_ne_top`,
`supBelow_singletons_nat_strictMono` and `iSup_supBelow_singletons_nat` record such a witness:
the cover of `ℕ` by its singletons, whose exhaustion is the chain of initial segments
`∅ ⊂ {0} ⊂ {0,1} ⊂ ⋯`.  It is infinite, strictly increasing, no stage is `⊤`, and the stages
cover.  It is written in `Set ℕ` so that it depends on no topology; `Opens` of the discrete
topology on `ℕ` is the same complete lattice.

## Why the exhaustion does not reduce `GluesAlongChain` to `GluesAlongWellOrderedCover`

`Stacks.DerivedGlueing.GluesAlongChain`, the hypothesis of [Stacks, Tag 0D6C] in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingOverACoveringCollection`, takes a
chain `𝒞` of opens each *carrying a solution* and asks for a solution over `sSup 𝒞`.  One might
hope to exhaust `𝒞` by the construction here and recurse.  Two obstructions, and both are real.

First, the exhaustion of `𝒞` is indexed by a well ordering of `𝒞` that has nothing to do with
inclusion, so its stages are suprema of arbitrary subsets of `𝒞` and in general **do not lie in
`𝒞`** — no solution is prescribed at a stage, which is exactly what
`Stacks.DerivedGlueing.GluesAlongWellOrderedCover` requires at *every* stage, limit stages
included.

Second, one cannot build the missing solution at a stage from the two-open case:
`Stacks.DerivedGlueing.GluesAlongTwoOpens` requires its *first* open to be a **member of the
collection of Situation 0D67**, and an earlier stage of the exhaustion is not one.  That is why
the Zorn argument of [Stacks, Tag 0D6C] works — it adjoins a single member of the collection at
each step, never a stage — and why the chain case is not eliminable from it.

What *is* true, and is the analogue here of the degeneracy criterion, is that a chain with a
greatest element needs no glueing at all: its supremum is that element, which already carries a
solution.  So `GluesAlongChain` too is only ever needed for a chain with no greatest element.

## Implementation notes

The exhaustion is indexed *strictly below*: `W_α = ⨆_{β < α} U_β`.  Indexing weakly below would
break the limit condition, since `⨆_{β ≤ α} U_β` exceeds `⨆_{γ < α} ⨆_{β ≤ γ} U_β` by `U_α`; that
is `Stacks.DerivedGlueing.not_limit_condition_of_le_singletons_nat`.  The
price of indexing strictly below is that the last member is never reached, which is why
`Stacks.DerivedGlueing.exists_wellOrderedCover_of_sSup_eq_top` indexes by `WithTop ℬ` rather than
by `ℬ`: the adjoined top is a stage whose predecessors are *all* of `ℬ`, so the stage at the
adjoined top is `sSup ℬ`.  No `NoMaxOrder` hypothesis on the well ordering of `ℬ` is needed, and
none is available, `ℬ` being arbitrary.

The well ordering of `ℬ` is Zermelo's theorem, `exists_wellFoundedLT`; it is the only
use of choice here, and `Classical.choice` is inside the axiom budget.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
-/

@[expose] public section

namespace Stacks.DerivedGlueing

universe v u

section CompleteLattice

variable {L : Type u} [CompleteLattice L] {E : Type v} [LinearOrder E]

/-- **The exhaustion of a family of elements indexed by a linear order.** The supremum of the
members strictly preceding a stage: `supBelow U α = ⨆_{β < α} U β`.

For a covering collection of opens this is the well ordered increasing cover that
[Stacks, Tag 0D6B] asks for; see the module documentation. -/
def supBelow (U : E → L) (α : E) : L := ⨆ (β : E) (_ : β < α), U β

/-- Every member preceding a stage is contained in that stage. -/
theorem le_supBelow (U : E → L) {β α : E} (h : β < α) : U β ≤ supBelow U α :=
  le_iSup₂_of_le β h le_rfl

/-- **The exhaustion is increasing.** This is the hypothesis `hsucc` of
`Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover` in the strong form the prescribed
transition isomorphisms of [Stacks, Tag 0D6B] are stated in: `W_β ⊆ W_α` for every `β < α`, not
only at the successors. -/
theorem supBelow_monotone (U : E → L) : Monotone (supBelow U) :=
  fun _ _ hβα => iSup₂_le fun _ hγ => le_supBelow U (lt_of_lt_of_le hγ hβα)

/-- **The exhaustion is increasing**, in the strict-inequality form in which
`Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover` consumes it. -/
theorem supBelow_le_supBelow_of_lt (U : E → L) {β α : E} (h : β < α) :
    supBelow U β ≤ supBelow U α :=
  iSup₂_le fun _ hγ => le_supBelow U (lt_trans hγ h)

/-- **At a successor the exhaustion grows by exactly one member.** If `β < α` and every stage
below `α` is at most `β` — that is, `β` is the immediate predecessor of `α`, which in a well
ordered set is what it means for `α` to be a successor — then `W_α = W_β ⊔ U_β`.

This is the shape in which the proof of [Stacks, Tag 0D6C] invokes the two-open case of
[Stacks, Tag 0D6A] at a successor stage: one member of the collection is adjoined to the open
reached so far. -/
theorem supBelow_eq_sup_of_isPred (U : E → L) {β α : E} (hβα : β < α)
    (hβ : ∀ γ : E, γ < α → γ ≤ β) : supBelow U α = supBelow U β ⊔ U β := by
  refine le_antisymm (iSup₂_le fun γ hγ => ?_)
    (sup_le (supBelow_le_supBelow_of_lt U hβα) (le_supBelow U hβα))
  rcases eq_or_lt_of_le (hβ γ hγ) with rfl | h
  · exact le_sup_right
  · exact le_sup_of_le_left (le_supBelow U h)

/-- **At a stage that is not a successor the exhaustion is the union of the earlier stages.**
This is the hypothesis `hlimit` of
`Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover`, and the exhaustion satisfies it with
no hypothesis at all on the family.

"`α` is not a successor" is the absence of an immediate predecessor, rendered exactly as that
theorem renders it.  The proof is that a stage `β < α` is then strictly below some `γ < α`, so
`U_β ⊆ W_γ`. -/
theorem supBelow_eq_iSup_supBelow_of_not_isPred (U : E → L) {α : E}
    (hα : ¬ ∃ β : E, β < α ∧ ∀ γ : E, γ < α → γ ≤ β) :
    supBelow U α = ⨆ (β : E) (_ : β < α), supBelow U β := by
  refine le_antisymm (iSup₂_le fun β hβ => ?_)
    (iSup₂_le fun β hβ => supBelow_le_supBelow_of_lt U hβ)
  obtain ⟨γ, hγα, hβγ⟩ : ∃ γ : E, γ < α ∧ β < γ := by
    by_contra h
    exact hα ⟨β, hβ, fun γ hγ => not_lt.mp fun hβγ => h ⟨γ, hγ, hβγ⟩⟩
  exact (le_supBelow U hβγ).trans (le_iSup₂_of_le γ hγα le_rfl)

/-- **A stage of an increasing cover that is not a successor is the union of the members of the
chain it contains.** This is the hypothesis that
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso` and
`Stacks.DerivedGlueing.HasGluingForHomsOver` impose on the open subset they are read over — that
it be the union of the members of the displayed collection contained in it — supplied at a limit
stage of a well ordered increasing cover for the collection consisting of *the stages of the
cover themselves*.

Together with `Stacks.DerivedGlueing.inf_eq_sSup_of_totallyOrdered` and
`Stacks.DerivedGlueing.totallyOrdered_range_of_wellOrderedCover` it supplies all three
hypotheses those predicates impose, so it pins down exactly what the limit stage of
[Stacks, Tag 0D6B]'s recursion needs from [Stacks, Tag 0D66] part (2): the sheaf condition for
*arbitrary* objects over a stage `W_α`, which is a union of earlier stages and in general is
neither `⊤` nor a member of the collection of Situation 0D67.  That relativized clause is
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covers`. -/
theorem eq_sSup_range_of_not_isPred {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α) {α : E}
    (hα : W α = ⨆ (β : E) (_ : β < α), W β) :
    W α = sSup {V | V ∈ Set.range W ∧ V ≤ W α} :=
  le_antisymm (hα.le.trans (iSup₂_le fun β hβ => le_sSup ⟨⟨β, rfl⟩, hmono β α hβ⟩))
    (sSup_le fun _ hV => hV.2)

/-- **The degeneracy criterion for an increasing cover.** If the index set has a greatest element
`g` and the stages cover, then `W_g = ⊤`: the cover displays the whole space.

So a datum of [Stacks, Tag 0D6B] over an index set with a greatest element is solved by the
prescribed object at that element, and certifies nothing about the transfinite content of the
tag.  See the module documentation. -/
theorem eq_top_of_isGreatest {W : E → L} (hmono : Monotone W) {g : E} (hg : ∀ α : E, α ≤ g)
    (hcover : (⨆ α : E, W α) = ⊤) : W g = ⊤ :=
  top_le_iff.mp (hcover.ge.trans (iSup_le fun α => hmono (hg α)))

end CompleteLattice

/-! ### Adjoining a last stage -/

section WithTop

variable {L : Type u} [CompleteLattice L] {ι : Type v} [LinearOrder ι]

/-- A family indexed by `ι`, read on `WithTop ι` by sending the adjoined top to `⊥`.  Only the
*predecessors* of the adjoined top are ever used, so the value there is immaterial. -/
def withTopExtend (U : ι → L) : WithTop ι → L := fun x => WithTop.recTopCoe ⊥ U x

omit [LinearOrder ι] in
/-- The extension `withTopExtend U` takes the value `⊥` at the adjoined top. -/
@[simp]
theorem withTopExtend_top (U : ι → L) : withTopExtend U ⊤ = ⊥ := rfl

omit [LinearOrder ι] in
/-- The extension `withTopExtend U` agrees with `U` on the members of `ι`. -/
@[simp]
theorem withTopExtend_coe (U : ι → L) (i : ι) : withTopExtend U (i : WithTop ι) = U i := rfl

/-- **Only the members of `ι` contribute to a stage of the exhaustion over `WithTop ι`.** The
adjoined top precedes no stage, so the stage at `α` is the supremum of the `U i` with
`i < α`. -/
theorem supBelow_withTopExtend_eq (U : ι → L) (α : WithTop ι) :
    supBelow (withTopExtend U) α = ⨆ (i : ι) (_ : (i : WithTop ι) < α), U i := by
  refine le_antisymm (iSup₂_le fun β hβ => ?_)
    (iSup₂_le fun i hi => le_supBelow (withTopExtend U) hi)
  induction β using WithTop.recTopCoe with
  | top => exact absurd hβ not_top_lt
  | coe i => exact le_iSup₂_of_le i hβ le_rfl

/-- **The stage at the adjoined top is the supremum of the whole family.** The predecessors of
the adjoined top of `WithTop ι` are exactly the members of `ι`, so the exhaustion reaches the
whole family there.  This is why
`Stacks.DerivedGlueing.exists_wellOrderedCover_of_sSup_eq_top` indexes by `WithTop ℬ`; see the
implementation notes. -/
theorem supBelow_withTopExtend_top (U : ι → L) :
    supBelow (withTopExtend U) ⊤ = ⨆ i : ι, U i := by
  rw [supBelow_withTopExtend_eq]
  exact le_antisymm (iSup₂_le fun i _ => le_iSup U i)
    (iSup_le fun i => le_iSup₂_of_le i (WithTop.coe_lt_top i) le_rfl)

/-- **The stages of the exhaustion over `WithTop ι` already cover at the adjoined top.** -/
theorem iSup_supBelow_withTopExtend (U : ι → L) :
    (⨆ α : WithTop ι, supBelow (withTopExtend U) α) = ⨆ i : ι, U i :=
  le_antisymm
    (iSup_le fun _ => (supBelow_monotone _ le_top).trans (supBelow_withTopExtend_top U).le)
    ((supBelow_withTopExtend_top U).ge.trans
      (le_iSup (fun α : WithTop ι => supBelow (withTopExtend U) α) ⊤))

/-- **Every stage of the exhaustion is the supremum of the members of the family it contains.**
This is what the vocabulary of `Stacks.DerivedGlueing.SolutionOver` asks of an open it is read
over. -/
theorem supBelow_withTopExtend_eq_sSup_range (U : ι → L) (α : WithTop ι) :
    supBelow (withTopExtend U) α =
      sSup {V | V ∈ Set.range U ∧ V ≤ supBelow (withTopExtend U) α} := by
  refine le_antisymm ?_ (sSup_le fun _ hV => hV.2)
  conv_lhs => rw [supBelow_withTopExtend_eq]
  exact iSup₂_le fun i hi => le_sSup ⟨⟨i, rfl⟩, le_supBelow (withTopExtend U) hi⟩

end WithTop



/-! ### The exhaustion of an arbitrary covering collection -/

/-- **Every covering collection is exhausted by a well ordered increasing family.** Let `ℬ` be a
collection of elements of a complete lattice with `sSup ℬ = ⊤`.  Then there are a well ordered
index set `E` and a family `W : E → L` such that

* `W` is increasing;
* `W α = ⨆_{β < α} W β` whenever `α` has no immediate predecessor;
* `⨆_α W α = ⊤`;
* each `W α` is the supremum of the members of `ℬ` contained in it;
* each member of `ℬ` is contained in some `W α`.

The first three clauses are exactly the hypotheses `hsucc`, `hlimit` and `hcover` of
`Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover`, so this is the bridge from the
collection `ℬ` of Situation 0D67 to the well ordered increasing cover of [Stacks, Tag 0D6B], and
it is the first step of the source's proof of [Stacks, Tag 0D6C].

The fourth clause is what the vocabulary of `Stacks.DerivedGlueing.SolutionOver` asks of an open
it is read over, and the fifth is what makes the prescribed object on a member of `ℬ` visible at
a single stage, so that no identification of the glued object with a prescribed object straddles
the chain.

The index set is `WithTop ℬ` for a well ordering of `ℬ` given by Zermelo's theorem; see the
implementation notes. -/
theorem exists_wellOrderedCover_of_sSup_eq_top {L : Type u} [CompleteLattice L] (ℬ : Set L)
    (hcover : sSup ℬ = ⊤) :
    ∃ (E : Type u) (_ : LinearOrder E) (_ : WellFoundedLT E) (W : E → L),
      (∀ β α : E, β < α → W β ≤ W α) ∧
        (∀ α : E, (¬ ∃ β : E, β < α ∧ ∀ γ : E, γ < α → γ ≤ β) →
            W α = ⨆ (β : E) (_ : β < α), W β) ∧
          (⨆ α : E, W α) = ⊤ ∧
            (∀ α : E, W α = sSup {V | V ∈ ℬ ∧ V ≤ W α}) ∧
              ∀ V ∈ ℬ, ∃ α : E, V ≤ W α := by
  classical
  obtain ⟨hlin, hwf⟩ := exists_wellFoundedLT (↥ℬ)
  let := hlin
  have := hwf
  refine ⟨WithTop ↥ℬ, inferInstance, inferInstance,
    supBelow (withTopExtend (fun V : ↥ℬ => (V : L))),
    fun _ _ h => supBelow_le_supBelow_of_lt _ h,
    fun _ hα => supBelow_eq_iSup_supBelow_of_not_isPred _ hα,
    ?_, fun α => ?_, fun V hV => ⟨⊤, ?_⟩⟩
  · rw [iSup_supBelow_withTopExtend, ← sSup_eq_iSup' ℬ]
    exact hcover
  · conv_lhs => rw [supBelow_withTopExtend_eq_sSup_range]
    simp
  · exact (le_iSup (fun V : ↥ℬ => (V : L)) ⟨V, hV⟩).trans
      (supBelow_withTopExtend_top (fun V : ↥ℬ => (V : L))).ge

/-! ### A non-degenerate witness: the cover of `ℕ` by its singletons -/

/-- **The exhaustion of the cover of `ℕ` by its singletons is the chain of initial segments.** -/
theorem supBelow_singletons_nat (n : ℕ) :
    supBelow (fun m : ℕ => ({m} : Set ℕ)) n = Set.Iio n := by
  ext k
  simp [supBelow, Set.mem_Iio]

/-- **No stage of that exhaustion is everything.**  Together with
`Stacks.DerivedGlueing.supBelow_singletons_nat_strictMono` and
`Stacks.DerivedGlueing.iSup_supBelow_singletons_nat` this certifies that the datum of
[Stacks, Tag 0D6B] has an inhabitant that is not degenerate: the chain is infinite and strictly
increasing, no stage is `⊤`, and the stages cover.  See the module documentation. -/
theorem supBelow_singletons_nat_ne_top (n : ℕ) :
    supBelow (fun m : ℕ => ({m} : Set ℕ)) n ≠ ⊤ := by
  rw [supBelow_singletons_nat]
  intro h
  exact absurd (h.ge (Set.mem_univ n)) (lt_irrefl n)

/-- **That exhaustion is strictly increasing**, so the chain has no repeated stage and in
particular is not of length one. -/
theorem supBelow_singletons_nat_strictMono :
    StrictMono (supBelow (fun m : ℕ => ({m} : Set ℕ))) := by
  intro m n hmn
  rw [supBelow_singletons_nat, supBelow_singletons_nat]
  exact Set.Iio_ssubset_Iio hmn

/-- **Indexing the exhaustion weakly below really does break the limit condition.**  At the
non-successor stage `0` of `ℕ` the weakly-below exhaustion of the singleton cover is `{0}`,
while the union of the earlier weakly-below stages is `∅`.  This is the fact the implementation
notes rest on, proved rather than asserted. -/
theorem not_limit_condition_of_le_singletons_nat :
    (⨆ (m : ℕ) (_ : m ≤ 0), ({m} : Set ℕ)) ≠
      ⨆ (k : ℕ) (_ : k < 0), ⨆ (m : ℕ) (_ : m ≤ k), ({m} : Set ℕ) := by
  intro h
  have h0 : (0 : ℕ) ∈ (⨆ (m : ℕ) (_ : m ≤ 0), ({m} : Set ℕ)) := by simp
  rw [h] at h0
  simp at h0

/-- **The stages of that exhaustion cover `ℕ`**, so the cover is not empty. -/
theorem iSup_supBelow_singletons_nat :
    (⨆ n : ℕ, supBelow (fun m : ℕ => ({m} : Set ℕ)) n) = ⊤ := by
  refine le_antisymm le_top fun k _ => ?_
  exact Set.mem_iUnion.mpr ⟨k + 1, by rw [supBelow_singletons_nat]; exact Nat.lt_succ_self k⟩

end Stacks.DerivedGlueing

end
