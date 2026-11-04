module

public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute

/-!
# Locally closed subspaces of quasi-sober and sober spaces (Stacks 0B31)

Stacks 0B31 records three permanence properties of the separation axioms of Section 5.8
under passage to a subspace:

1. a subspace of a Kolmogorov space is Kolmogorov;
2. a *locally closed* subspace of a quasi-sober space is quasi-sober;
3. a locally closed subspace of a sober space is sober.

Part (1) is Mathlib's instance `Subtype.t0Space`, which already carries the tag, so it is
not restated here. Parts (2) and (3) are stated for a set `Y : Set X` satisfying Mathlib's
`IsLocallyClosed`, i.e. `Y = U ∩ F` with `U` open and `F` closed; the Stacks Project's
"sober" is Mathlib's `QuasiSober` together with `T0Space`, so part (3) is the conjunction
of part (2) with `Subtype.t0Space`.

The proof of (2) is the composite of two Mathlib facts: an open subspace of a quasi-sober
space is quasi-sober (`Topology.IsOpenEmbedding.quasiSober`), and the intersection of a
quasi-sober set with a closed set is quasi-sober
(`QuasiSober.inter_of_isClosed_of_quasiSober_left`).
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- **Stacks 0B31 (2).** A locally closed subspace of a quasi-sober space is quasi-sober. -/
@[stacks 0B31 "(2)"]
theorem IsLocallyClosed.quasiSober [QuasiSober X] {Y : Set X} (hY : IsLocallyClosed Y) :
    QuasiSober Y := by
  obtain ⟨U, F, hU, hF, rfl⟩ := hY
  have := hU.isOpenEmbedding_subtypeVal.quasiSober
  exact QuasiSober.inter_of_isClosed_of_quasiSober_left U hF

/-- **Stacks 0B31 (3).** A locally closed subspace of a sober space is sober, sobriety being
`QuasiSober` together with `T0Space`. -/
@[stacks 0B31 "(3)"]
theorem IsLocallyClosed.quasiSober_and_t0Space [QuasiSober X] [T0Space X] {Y : Set X}
    (hY : IsLocallyClosed Y) : QuasiSober Y ∧ T0Space Y :=
  ⟨hY.quasiSober, Subtype.t0Space⟩
