module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving

/-!
# A pro-isomorphism from inverses that exist only after an unspecified refinement

A morphism `α : X ⟶ Y` of inverse systems indexed by `ℕᵒᵖ` is an isomorphism of pro-objects as
soon as **every** level `n` admits *some* later level `m` carrying a map `s : Y_m ⟶ X_n` whose two
round trips are the transition maps:

`α_m ≫ s = (X_m ⟶ X_n)` and `s ≫ α_n = (Y_m ⟶ Y_n)`.

That is the conclusion [Stacks, Tag 0G3D] hands back, and it is weaker than what
`InverseSequence.ProIso.Interleaving` asks for: the latter wants one strictly increasing index
sequence `n₀ < n₁ < n₂ < ⋯` with the maps placed at prescribed stages. This file closes that gap
by **building the index sequence by recursion** from the per-level existence statement: the stage
`n_{2i+1}` is chosen past the level the hypothesis produces at `n_{2i}`, and `n_{2i+2}` is its
successor.

The recursion is the reason this is not a reindexing. A uniform, explicit bound — as in
`Stacks.Algebraization.proIso_globalSpanQuotientSystem_adicQuotientSystem`, whose interleaving
bound is the pigeonhole exponent `rn + 1` — lets the index sequence be written down in closed
form. A bound coming from Artin–Rees is only existential, so each stage has to be chosen after
the previous one has been fixed.

## Main definitions

* `InverseSequence.ProIso.eventualIdx` — the index sequence, built by recursion from the function
  that assigns to a level the later level at which an inverse exists.
* `InverseSequence.ProIso.Interleaving.ofExistsProInverse` — the interleaving.

## Main results

* `InverseSequence.ProIso.proIsoOfExistsProInverse` — **the pro-isomorphism**.

## Implementation notes

`eventualIdx` is a function of the choice function alone, so it is an ordinary structural
recursion on `ℕ` and needs no well-founded machinery: the parity of the predecessor decides which
of the two clauses applies, and both clauses increase the value, which is what makes the sequence
strictly increasing.

The hypothesis is stated with the transition maps spelled `X.map (homOfLE h).op`, which is the
spelling of `NoetherianAdicCompletion.HasEventualInverses` and of the conclusion of
[Stacks, Tag 0G3D], rather than through `InverseSequence.tr`; the two are the same by definition.

Transition maps of an inverse system depend on an inequality only through the proposition it
proves, so the identities below hold for any proofs of the inequalities involved; proof
irrelevance makes the two spellings of a transition map definitionally equal, and no transport is
needed.

## References

* [Stacks Project, Tag 0G3D](https://stacks.math.columbia.edu/tag/0G3D)
* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L)
-/

section

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u

namespace InverseSequence.ProIso

/-- **The index sequence of the interleaving built from per-level inverses.** The stage `2i + 1`
is taken past the level `g` assigns to the stage `2i`, and the stage `2i + 2` is its successor. -/
def eventualIdx (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if n % 2 = 0 then max (g (eventualIdx g n)) (eventualIdx g n + 1)
      else eventualIdx g n + 1

/-- Both clauses of the recursion increase the value. -/
theorem lt_eventualIdx_succ (g : ℕ → ℕ) (n : ℕ) :
    eventualIdx g n < eventualIdx g (n + 1) := by
  rw [eventualIdx]
  split
  · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  · exact Nat.lt_succ_self _

/-- The index sequence `eventualIdx g` is strictly increasing. -/
theorem strictMono_eventualIdx (g : ℕ → ℕ) : StrictMono (eventualIdx g) :=
  strictMono_nat_of_lt_succ (lt_eventualIdx_succ g)

/-- At an even stage the recursion takes a maximum, so the level `g` assigns to that stage is
reached by the next stage. -/
theorem le_eventualIdx_odd (g : ℕ → ℕ) (i : ℕ) :
    g (eventualIdx g (2 * i)) ≤ eventualIdx g (2 * i + 1) := by
  rw [eventualIdx, ite_eq_left (Nat.mul_mod_right 2 i)]
  exact le_max_left _ _

/-- The odd stages are below the even stage that follows them. -/
theorem eventualIdx_odd_le_even (g : ℕ → ℕ) (i : ℕ) :
    eventualIdx g (2 * i + 1) ≤ eventualIdx g (2 * i + 2) :=
  le_of_lt (lt_eventualIdx_succ g (2 * i + 1))

/-- Transition maps of an inverse system indexed by `ℕᵒᵖ` compose, in the spelling
`X.map (homOfLE h).op`. -/
theorem map_homOfLE_op_comp {D : Type u} [Category.{v} D] (F : ℕᵒᵖ ⥤ D) {a b c : ℕ} (h₁ : b ≤ a)
    (h₂ : c ≤ b) :
    F.map (homOfLE h₁).op ≫ F.map (homOfLE h₂).op = F.map (homOfLE (h₂.trans h₁)).op := by
  rw [← F.map_comp]
  rfl

section Composites

variable {D : Type u} [Category.{v} D] {X Y : ℕᵒᵖ ⥤ D} (α : X ⟶ Y) {g : ℕ → ℕ}
  (hg : ∀ n : ℕ, n ≤ g n) (s : ∀ n : ℕ, Y.obj (op (g n)) ⟶ X.obj (op n))

/-- **A transition map of `X` followed by `α`, followed by a transition map of `Y` followed by an
inverse, is a transition map of `X`.** All indices are free: no property of the index sequence
enters. -/
theorem comp_eventualInverse_fwd_bwd
    (hs₁ : ∀ n : ℕ, α.app (op (g n)) ≫ s n = X.map (homOfLE (hg n)).op)
    {a b c : ℕ} (h₁ : b ≤ a) (h₂ : g c ≤ b) (h₃ : c ≤ a) :
    (X.map (homOfLE h₁).op ≫ α.app (op b)) ≫ (Y.map (homOfLE h₂).op ≫ s c) =
      X.map (homOfLE h₃).op := by
  rw [Category.assoc, ← Category.assoc (α.app (op b)), ← α.naturality (homOfLE h₂).op,
    Category.assoc, hs₁ c, map_homOfLE_op_comp, map_homOfLE_op_comp]

/-- **A transition map of `Y` followed by an inverse, followed by a transition map of `X` followed
by `α`, is a transition map of `Y`.** -/
theorem comp_eventualInverse_bwd_fwd
    (hs₂ : ∀ n : ℕ, s n ≫ α.app (op n) = Y.map (homOfLE (hg n)).op)
    {a b c : ℕ} (h₁ : g b ≤ a) (h₂ : c ≤ b) (h₃ : c ≤ a) :
    (Y.map (homOfLE h₁).op ≫ s b) ≫ (X.map (homOfLE h₂).op ≫ α.app (op c)) =
      Y.map (homOfLE h₃).op := by
  rw [Category.assoc, α.naturality (homOfLE h₂).op,
    ← Category.assoc (s b), hs₂ b, map_homOfLE_op_comp, map_homOfLE_op_comp]

end Composites

namespace Interleaving

/-- **The interleaving built from per-level inverses**, along the index sequence
`InverseSequence.ProIso.eventualIdx`. The forward map at stage `i` is a transition map of `X`
followed by `α`; the backward map is a transition map of `Y` followed by the given inverse. -/
def ofExistsProInverse {D : Type u} [Category.{v} D] {X Y : ℕᵒᵖ ⥤ D} (α : X ⟶ Y)
    {g : ℕ → ℕ} (hg : ∀ n : ℕ, n ≤ g n)
    (s : ∀ n : ℕ, Y.obj (op (g n)) ⟶ X.obj (op n))
    (hs₁ : ∀ n : ℕ, α.app (op (g n)) ≫ s n = X.map (homOfLE (hg n)).op)
    (hs₂ : ∀ n : ℕ, s n ≫ α.app (op n) = Y.map (homOfLE (hg n)).op) :
    Interleaving X Y where
  idx := eventualIdx g
  idx_strictMono := strictMono_eventualIdx g
  fwd i := X.map (homOfLE (eventualIdx_odd_le_even g i)).op ≫
    α.app (op (eventualIdx g (2 * i + 1)))
  bwd i := Y.map (homOfLE (le_eventualIdx_odd g i)).op ≫ s (eventualIdx g (2 * i))
  fwd_bwd _ := comp_eventualInverse_fwd_bwd α hg s hs₁ _ _ _
  bwd_fwd _ := comp_eventualInverse_bwd_fwd α hg s hs₂ _ _ _

end Interleaving

/-- **A morphism of inverse systems indexed by `ℕᵒᵖ` whose every level admits an inverse after
some later level is an isomorphism of pro-objects.** This is the shape in which
[Stacks, Tag 0G3D] delivers a pro-isomorphism: a per-level existence statement, with no uniform
or explicit bound on how far the level has to be refined.

The index sequence of the interleaving is built by recursion,
`InverseSequence.ProIso.eventualIdx` applied to the function the hypothesis provides. -/
def proIsoOfExistsProInverse {D : Type u} [Category.{v} D] {X Y : ℕᵒᵖ ⥤ D} (α : X ⟶ Y)
    (H : ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m) (σ : Y.obj (op m) ⟶ X.obj (op n)),
      α.app (op m) ≫ σ = X.map (homOfLE hnm).op ∧
        σ ≫ α.app (op n) = Y.map (homOfLE hnm).op) :
    InverseSequence.ProIso X Y := by
  choose g hg s hs₁ hs₂ using H
  exact (Interleaving.ofExistsProInverse α hg s hs₁ hs₂).proIso

end InverseSequence.ProIso

end

end
