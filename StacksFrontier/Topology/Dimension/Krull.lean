module

public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Krull dimension of a topological space, and at a point (Stacks 0055)

Stacks 0055 makes four definitions. Parts (1) and (2), a chain of irreducible closed subsets
of `X` and its length, are Mathlib's `LTSeries (TopologicalSpace.IrreducibleCloseds X)` and
`RelSeries.length`; part (3), the dimension `dim X` as the supremum of those lengths, is
Mathlib's `topologicalKrullDim`, which is *defined* as that supremum. None of the three needs
a declaration here. What part (3) does add over the definition is the boundary convention,
that `dim X = -∞` exactly when `X` is empty: this is `topologicalKrullDim_eq_bot_iff_isEmpty`,
since a nonempty space has the irreducible closed subset `closure {x}`.

Part (4), the dimension of `X` at a point `x`, is not in Mathlib. Stacks defines it as the
minimum of `dim U` over the open neighbourhoods `U` of `x`. We take the infimum in
`WithBot ℕ∞`, which is well-founded, and `topologicalKrullDimAt_isLeast` proves that the
infimum is attained, i.e. that it really is Stacks' minimum.
-/

@[expose] public section

open TopologicalSpace

variable (X : Type*) [TopologicalSpace X]

/-- A nonempty space has an irreducible closed subset, namely a point closure. -/
private theorem nonempty_irreducibleCloseds_of_nonempty [Nonempty X] :
    Nonempty (IrreducibleCloseds X) :=
  ⟨⟨closure {Classical.arbitrary X}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

/-- **Stacks 0055 (3).** The Krull dimension of `X` is `-∞` exactly when `X` is empty; for a
nonempty space `closure {x}` is an irreducible closed subset, so the supremum is taken over a
nonempty family. -/
@[stacks 0055 "(3)"]
theorem topologicalKrullDim_eq_bot_iff_isEmpty :
    topologicalKrullDim X = ⊥ ↔ IsEmpty X := by
  rw [topologicalKrullDim, Order.krullDim_eq_bot_iff]
  exact ⟨fun h ↦ ⟨fun x ↦ have : Nonempty X := ⟨x⟩
      h.elim (nonempty_irreducibleCloseds_of_nonempty X).some⟩,
    fun h ↦ ⟨fun S ↦ h.elim S.isIrreducible.nonempty.choose⟩⟩

/-- **Stacks 0055 (4).** The Krull dimension of `X` at a point `x`: the infimum of the Krull
dimensions of the open neighbourhoods of `x`. It is a minimum, by
`topologicalKrullDimAt_isLeast`. -/
@[stacks 0055 "(4)", ega "0 14.1.2" "dim_x formula", sga "3 VIB 1.5", sga "7 XV 1.2"]
noncomputable def topologicalKrullDimAt (x : X) : WithBot ℕ∞ :=
  ⨅ U : {U : Set X // x ∈ U ∧ IsOpen U}, topologicalKrullDim (↥U.val)

/-- The Krull dimension of a space at a point is nonnegative: every open neighbourhood of the
point contains the point, so is nonempty, and the Krull dimension of a nonempty space is at
least `0`.

The space is implicit here, so that the lemma applies to the point alone. -/
theorem topologicalKrullDimAt_nonneg {X : Type*} [TopologicalSpace X] (x : X) :
    (0 : WithBot ℕ∞) ≤ topologicalKrullDimAt X x := by
  rw [topologicalKrullDimAt]
  refine le_iInf fun U ↦ ?_
  have : Nonempty ↥U.val := ⟨⟨x, U.prop.1⟩⟩
  have := nonempty_irreducibleCloseds_of_nonempty ↥U.val
  simpa [topologicalKrullDim] using Order.krullDim_nonneg

/-- **Stacks 0055 (4).** `topologicalKrullDimAt X x` is the *least* element of the set of
Krull dimensions of open neighbourhoods of `x`, which is Stacks' phrasing of part (4) as a
minimum. The infimum is attained because `WithBot ℕ∞` is well-founded. -/
@[stacks 0055 "(4)", ega "0 14.1.2" "dim_x(X)=inf_U dim(U)", sga "3 VIB 1.5" "partial"]
theorem topologicalKrullDimAt_isLeast (x : X) :
    IsLeast
      {d : WithBot ℕ∞ |
        ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ d = topologicalKrullDim (↥U)}
      (topologicalKrullDimAt X x) := by
  set f : {U : Set X // x ∈ U ∧ IsOpen U} → WithBot ℕ∞ :=
    fun U ↦ topologicalKrullDim (↥U.val)
  have : Nonempty {U : Set X // x ∈ U ∧ IsOpen U} :=
    ⟨⟨Set.univ, Set.mem_univ x, isOpen_univ⟩⟩
  obtain ⟨i, hi⟩ := ciInf_mem f
  refine ⟨⟨i.val, i.prop.1, i.prop.2, by simpa [topologicalKrullDimAt, f] using hi.symm⟩, ?_⟩
  rintro d ⟨U, hxU, hU, rfl⟩
  exact iInf_le f ⟨U, hxU, hU⟩

section NeBot

variable {X : Type*} [TopologicalSpace X]

/-- The local dimension of a space at a point is never `⊥`: the point lies in every open
neighbourhood whose dimension the infimum ranges over, so none of them is empty. -/
theorem topologicalKrullDimAt_ne_bot (x : X) : topologicalKrullDimAt X x ≠ ⊥ := by
  obtain ⟨⟨U, hxU, _, hdim⟩, _⟩ := topologicalKrullDimAt_isLeast X x
  intro hbot
  exact ((topologicalKrullDim_eq_bot_iff_isEmpty (↥U)).mp (by rw [← hdim, hbot])).false ⟨x, hxU⟩

end NeBot

/-- The Krull dimension of a space at a point is at most the Krull dimension of the space: the
infimum defining the former ranges over the open neighbourhoods of the point, and `Set.univ` is
one of them.

The space is implicit here, so that the lemma applies to the point alone. -/
theorem topologicalKrullDimAt_le_topologicalKrullDim {X : Type*} [TopologicalSpace X] (x : X) :
    topologicalKrullDimAt X x ≤ topologicalKrullDim X :=
  ((topologicalKrullDimAt_isLeast X x).2 ⟨Set.univ, Set.mem_univ x, isOpen_univ, rfl⟩).trans
    (topologicalKrullDim_subspace_le X Set.univ)

section Discrete

variable {X : Type*} [TopologicalSpace X]

/-- A nonempty discrete space has topological Krull dimension zero: every irreducible closed
subset is a point closure, so no chain is longer than a single term, and a nonempty space has
at least one such subset. -/
@[ega "0 14.1.12" "dim(X) = 0"]
theorem topologicalKrullDim_eq_zero_of_discreteTopology_nonempty
    [DiscreteTopology X] [Nonempty X] : topologicalKrullDim X = 0 := by
  have := nonempty_irreducibleCloseds_of_nonempty X
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology X) Order.krullDim_nonneg

end Discrete

section Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Auxiliary form of `topologicalKrullDimAt_le_of_isEmbedding`, needed before its place. -/
private theorem topologicalKrullDimAt_le_of_isEmbedding_aux {f : X → Y}
    (hf : Topology.IsEmbedding f) (x : X) :
    topologicalKrullDimAt X x ≤ topologicalKrullDimAt Y (f x) := by
  refine le_iInf fun V ↦ iInf_le_of_le ⟨f ⁻¹' V.1, V.2.1, V.2.2.preimage hf.continuous⟩ ?_
  let r : (f ⁻¹' V.1) → V.1 := fun z ↦ ⟨f z.1, z.2⟩
  exact (Topology.IsInducing.subtypeVal.of_comp_iff.mp
    (hf.isInducing.comp .subtypeVal) : Topology.IsInducing r).topologicalKrullDim_le


/-- The Krull dimension at a point depends only on a neighbourhood of that point: along an
open embedding `f`, the dimensions at `x` and at `f x` agree. The two infima are cofinal in
each other, since `f '' U` is an open neighbourhood of `f x` homeomorphic to `U`, and `f ⁻¹' V`
is an open neighbourhood of `x` whose image `f '' (f ⁻¹' V)` is a subspace of `V`. -/
theorem Topology.IsOpenEmbedding.topologicalKrullDimAt_eq {f : X → Y} (hf : IsOpenEmbedding f)
    (x : X) : topologicalKrullDimAt Y (f x) = topologicalKrullDimAt X x := by
  refine le_antisymm
    (le_iInf fun U ↦ iInf_le_of_le ⟨f '' U.1, ⟨x, U.2.1, rfl⟩, hf.isOpenMap _ U.2.2⟩ ?_)
    (topologicalKrullDimAt_le_of_isEmbedding_aux hf.isEmbedding x)
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (hf.isEmbedding.homeomorphImage U.1).isHomeomorph).ge

/-- The Krull dimension at a point is a homeomorphism invariant: the pointwise form of
`IsHomeomorph.topologicalKrullDim_eq`. -/
theorem topologicalKrullDimAt_eq_of_homeomorph (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt X x = topologicalKrullDimAt Y (e x) :=
  (e.isOpenEmbedding.topologicalKrullDimAt_eq x).symm

end Homeomorph

section Embedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The Krull dimension at a point does not increase along an embedding.** An open
neighbourhood of the image point pulls back to an open neighbourhood of the point, and that
preimage is a subspace of the neighbourhood it came from; so every term of the infimum on the
right dominates some term of the infimum on the left. -/
theorem topologicalKrullDimAt_le_of_isEmbedding {f : X → Y} (hf : Topology.IsEmbedding f)
    (x : X) : topologicalKrullDimAt X x ≤ topologicalKrullDimAt Y (f x) :=
  topologicalKrullDimAt_le_of_isEmbedding_aux hf x

end Embedding

section Subspace

variable {X : Type*} [TopologicalSpace X]

/-- **The Krull dimension of a subspace is monotone in the subset.** Mathlib's
`topologicalKrullDim_subspace_le` compares a subspace with the whole space; this is the
comparison of two subsets of one space, the inclusion of the smaller into the larger being an
embedding and hence inducing. -/
@[ega "0 14.1.4" "more general"]
theorem topologicalKrullDim_le_of_subset {S T : Set X} (h : S ⊆ T) :
    topologicalKrullDim S ≤ topologicalKrullDim T :=
  (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-- **The dimension of a subset does not depend on which ambient subspace it is read in.** For
`A ⊆ Y`, the subspace `A` of `X` and the subspace `Subtype.val ⁻¹' A` of `Y` are homeomorphic. -/
theorem topologicalKrullDim_preimage_val (Y A : Set X) (hA : A ⊆ Y) :
    topologicalKrullDim ((Subtype.val : Y → X) ⁻¹' A) = topologicalKrullDim A :=
  let e : ((Subtype.val : Y → X) ⁻¹' A : Set Y) ≃ₜ (A : Set X) :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hA y.2⟩, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  e.isHomeomorph.topologicalKrullDim_eq

end Subspace

