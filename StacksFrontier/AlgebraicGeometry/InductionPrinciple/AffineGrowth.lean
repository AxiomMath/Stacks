module

public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction

/-!
# Growing a quasi-compact open to the whole scheme by affine opens

Let `X` be a quasi-compact scheme and `U ⊆ X` an open. A property of the opens of `X` which holds
at `U` and which passes from an open `W ⊇ U` and an affine open `V` to `W ⊔ V` holds at `⊤`.

This is the step that [Stacks, Tag 09IM] compresses into a sentence: *"Since `X` is quasi-compact
there exists an integer `m` such that `X = U ∪ V₁ ∪ ⋯ ∪ V_m` for some affine opens `V_j` of `X`.
Arguing by induction on `m` we see that we may assume `m = 1`."* The content is that a lemma
whose conclusion is stable under adjoining one affine open to an open containing `U` needs to be
proved only for `X = U ∪ V` with `V` affine.

## Main results

* `Stacks.AlgebraicGeometry.InductionPrinciple.prop_top_of_affineGrowth`.

## Implementation notes

This is *not* [Stacks, Tag 08DR], `induction_isCompact_open` in
`StacksFrontier/AlgebraicGeometry/InductionPrinciple/Basic.lean`, although the Finset recursion is
the same one. Two differences, and both matter for the consumer this is written for:

* the base case is the given open `U`, not an affine open — in 09IM the lifting problem is solved
  over `U` by the given object itself, and there is nothing to say over an affine open disjoint
  from `U`;
* the step is a *two*-term glueing, from `W` and `V` to `W ⊔ V`, with no hypothesis at `W ⊓ V`.
  Tag 08DR's step needs the intersection because it reconstructs an object over `W ⊔ V` out of
  three given ones; 09IM's does not, because over the affine `V` the object is produced from
  scratch by [Stacks, Tag 08EK] applied to the open `W ⊓ V` of `V`, and only the *overlap
  identification* is needed, which [Stacks, Tag 08DG] supplies.

Accordingly nothing here is stated about quasi-separatedness: the recursion only ever forms
`W ⊔ V`, never `W ⊓ V`, so the intersections never have to be quasi-compact.

The hypothesis `U ≤ W` is carried through the recursion because a consumer needs it — the lifting
data of 09IM lives over an open containing `U`, and the step has to restrict it to `W ⊓ V`.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.InductionPrinciple

variable {X : Scheme.{u}}

/-- **Growing `U` to `⊤` by affine opens.** Let `X` be quasi-compact, `U ⊆ X` an open and `Q` a
property of the opens of `X`. If `Q` holds at `U`, and if `Q` passes from an open `W` containing
`U` and an affine open `V` to `W ⊔ V`, then `Q` holds at `⊤`.

This is the induction of [Stacks, Tag 09IM]'s proof: it reduces that lemma to the case
`X = U ∪ V` with `V` affine. -/
public theorem prop_top_of_affineGrowth [CompactSpace X] (Q : X.Opens → Prop) (U : X.Opens)
    (hU : Q U)
    (step : ∀ W : X.Opens, U ≤ W → ∀ V : X.Opens, IsAffineOpen V → Q W → Q (W ⊔ V)) :
    Q ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top (X := X)
  have key : ∀ t : Finset X.affineOpens,
      U ≤ U ⊔ (⨆ V ∈ t, (V : X.Opens)) ∧ Q (U ⊔ (⨆ V ∈ t, (V : X.Opens))) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using hU
    | @insert a t _ ih =>
      obtain ⟨hle, hQ⟩ := ih
      refine ⟨le_sup_left, ?_⟩
      have hrw : U ⊔ (⨆ V ∈ insert a t, (V : X.Opens)) =
          (U ⊔ (⨆ V ∈ t, (V : X.Opens))) ⊔ (a : X.Opens) := by
        rw [Finset.iSup_insert, ← sup_assoc, sup_right_comm]
      rw [hrw]
      exact step _ hle _ a.2 hQ
  have hfull := (key s).2
  rwa [hs, sup_top_eq] at hfull

end Stacks.AlgebraicGeometry.InductionPrinciple

end
