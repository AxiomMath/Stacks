module

public import Mathlib.Data.ENat.SuccOrder
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Topology.NowhereDense.Defs
public import StacksFrontier.Topology.Dimension.Krull

/-!
# A nowhere dense closed subset has strictly smaller dimension

In a Noetherian space `X`, a closed subset `S` with empty interior misses every irreducible
component: an irreducible component of a Noetherian space contains a nonempty open subset of
`X` (`TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`,
Stacks 0052 (3)), so a component inside `S` would make `interior S` nonempty. Hence a maximal
chain of irreducible closed subsets of `S`, read in `X`, can always be extended upwards by one
step, and `dim S` is smaller than `dim X` by at least one.

## Main results

* `IsClosed.isNowhereDense_iff_forall_irreducibleComponents_not_subset`: for a closed subset of
  a Noetherian space, nowhere density is exactly missing every irreducible component. This is
  the criterion in which the hypothesis is checkable.
* `IsNowhereDense.not_isMax_of_subset`: an irreducible closed subset of a nowhere dense closed
  set is never maximal among the irreducible closed subsets of the ambient Noetherian space.
* `IsNowhereDense.topologicalKrullDim_add_one_le`: `dim S + 1 ≤ dim X`. This is the sharp
  statement, and needs no finiteness or nonemptiness hypothesis, by the conventions
  `dim ∅ = -∞` and `-∞ + 1 = -∞`.
* `IsNowhereDense.topologicalKrullDim_lt`: the strict inequality `dim S < dim X`, for `X`
  nonempty and finite-dimensional. Both side conditions are necessary: for `X` empty both
  sides are `-∞`, and for `dim X = ∞` a nowhere dense closed subset can again have
  dimension `∞`.
* `IsNowhereDense.toNat_unbotD_topologicalKrullDim_lt`: the same strict inequality between the
  two dimensions read as natural numbers, which is the form a dimension-descending induction
  consumes.
* `IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ` and
  `IsNowhereDense.topologicalKrullDim_nonpos_of_le_one`: the bounded forms, which need no side
  condition because the bound on `dim X` supplies the finite-dimensionality.
* `toNat_unbotD_topologicalKrullDim_lt_of_isNowhereDense_subspace`: the relative form, between
  two subsets `A ⊆ Y` of a common ambient space with `A` nowhere dense in `Y`, using
  `topologicalKrullDim_preimage_val` (in `StacksFrontier.Topology.Dimension.Krull`) to read the
  dimension of `A` in either ambient space.
* `isNowhereDense_preimage_val_iff_forall_irreducibleComponents`: nowhere density *inside a
  subspace* `Y`, as a condition on the irreducible components of `Y`. This is the form in which
  the relative hypothesis of the previous statement is checkable, and the form that makes the
  gap between it and absolute nowhere density visible: the components of `Y` are not the
  components of the ambient space, so a set nowhere dense in the ambient space can contain one
  of them.
* `topologicalKrullDim_univ`: the subspace `Set.univ` has the dimension of the whole space.
  Together with the previous statement this is the one case in which absolute nowhere density
  *does* give the relative one, namely `Y = Set.univ`.

## Implementation notes

The finite-dimensionality hypothesis of the strict forms is not an artefact of the proof. Give
`ℕ ∪ {∗}` the topology whose closed sets are the initial segments `{0, …, n}`, all of `ℕ`, and
the whole space. It is Noetherian, `ℕ` is closed in it, and `ℕ` is nowhere dense because every
nonempty open set contains `∗`; both dimensions are `∞`.

The natural-number form needs the ambient dimension to be nonzero, not merely the ambient space
to be nonempty: a nonempty `X` of dimension `0` with `S = ∅` has `dim S = -∞ < 0 = dim X`, while
both read as `0` after `WithBot.unbotD 0` and `ENat.toNat`. That extra hypothesis is exactly the
one a descending induction has in hand in its inductive step.
-/

@[expose] public section

open Order Set Topology TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- An element of `WithBot ℕ∞` that is neither `-∞` nor `∞` is a natural number. -/
private theorem exists_natCast_of_ne_bot_of_ne_top {x : WithBot ℕ∞} (hb : x ≠ ⊥) (ht : x ≠ ⊤) :
    ∃ n : ℕ, x = (n : WithBot ℕ∞) := by
  cases hx : x with
  | bot => exact absurd hx hb
  | coe e =>
    cases e with
    | top => exact absurd hx ht
    | coe n => exact ⟨n, rfl⟩

/-- A nowhere dense closed set contains no irreducible component of a Noetherian space. -/
private theorem IsNowhereDense.false_of_subset_irreducibleComponent [NoetherianSpace X]
    {S : Set X} (hnd : IsNowhereDense S) (hclosed : IsClosed S) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hZS : Z ⊆ S) : False := by
  obtain ⟨o, hoopen, ⟨x, hx⟩, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  rw [IsNowhereDense, hclosed.closure_eq] at hnd
  simpa [hnd] using interior_maximal (hoZ.trans hZS) hoopen hx

/-- **For a closed subset of a Noetherian space, nowhere density is exactly missing every
irreducible component.** This is the criterion a supplier of the nowhere-density hypothesis
checks: in a Noetherian space an irreducible component contains a nonempty open set, so a
component inside `S` gives `S` interior; conversely a nonempty open subset of `S` meets some
component, and a nonempty open subset of an irreducible set is dense in it, so that whole
component lies in `S`. -/
theorem IsClosed.isNowhereDense_iff_forall_irreducibleComponents_not_subset [NoetherianSpace X]
    {S : Set X} (hclosed : IsClosed S) :
    IsNowhereDense S ↔ ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ S := by
  constructor
  · exact fun hnd Z hZ hZS => hnd.false_of_subset_irreducibleComponent hclosed hZ hZS
  · intro h
    rw [IsNowhereDense, hclosed.closure_eq]
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    refine h (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x) ?_
    have hmeet : (irreducibleComponent x ∩ interior S).Nonempty :=
      ⟨x, mem_irreducibleComponent, hx⟩
    refine le_trans (subset_closure_inter_of_isPreirreducible_of_isOpen
      (isIrreducible_irreducibleComponent (x := x)).isPreirreducible isOpen_interior hmeet) ?_
    exact hclosed.closure_subset_iff.mpr (Set.inter_subset_right.trans interior_subset)

/-- **An irreducible closed subset of a nowhere dense closed set is never maximal.** In a
Noetherian space a maximal irreducible closed subset is an irreducible component, and an
irreducible component contains a nonempty open subset of the ambient space, which a nowhere
dense set does not. -/
theorem IsNowhereDense.not_isMax_of_subset [NoetherianSpace X] {S : Set X}
    (hnd : IsNowhereDense S) (hclosed : IsClosed S) (A : IrreducibleCloseds X)
    (hA : (A : Set X) ⊆ S) : ¬ IsMax A := by
  intro hmax
  obtain ⟨u, hu, hAu⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (A : Set X) A.isIrreducible
  have hle : A ≤ (⟨u, hu.1, isClosed_of_mem_irreducibleComponents u hu⟩ : IrreducibleCloseds X) :=
    hAu
  have heq : u = (A : Set X) := Set.Subset.antisymm (hmax hle) hAu
  exact hnd.false_of_subset_irreducibleComponent hclosed hu (heq ▸ hA)

/-- **A nowhere dense closed subset of a Noetherian space has dimension at least one less.**
No finiteness or nonemptiness hypothesis is needed: when `S` is empty both `dim S` and
`dim S + 1` are `-∞`, and when `dim S = ∞` so is `dim X`. -/
theorem IsNowhereDense.topologicalKrullDim_add_one_le [NoetherianSpace X] {S : Set X}
    (hnd : IsNowhereDense S) (hclosed : IsClosed S) :
    topologicalKrullDim S + 1 ≤ topologicalKrullDim X := by
  have hmono : topologicalKrullDim S ≤ topologicalKrullDim X :=
    topologicalKrullDim_subspace_le X S
  rcases eq_or_ne (topologicalKrullDim S) ⊥ with h | hbot
  · rw [h]; simp
  rcases eq_or_ne (topologicalKrullDim S) ⊤ with h | htop
  · rw [le_antisymm le_top (le_trans (le_of_eq h.symm) hmono)]; exact le_top
  obtain ⟨n, h⟩ := exists_natCast_of_ne_bot_of_ne_top hbot htop
  have hn : (n : WithBot ℕ∞) ≤ krullDim (IrreducibleCloseds S) := h.ge
  obtain ⟨p, hp⟩ := le_krullDim_iff.mp hn
  have hstrict : StrictMono
      (IrreducibleCloseds.map (Subtype.val : S → X) IsInducing.subtypeVal.continuous) :=
    IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  set F := IrreducibleCloseds.map (Subtype.val : S → X) IsInducing.subtypeVal.continuous
    with hFdef
  have hlast : (F p.last : Set X) ⊆ S := by
    rw [hFdef, IrreducibleCloseds.coe_map]
    exact hclosed.closure_subset_iff.mpr (by rintro x ⟨y, -, rfl⟩; exact y.2)
  obtain ⟨Z, hZ⟩ := not_isMax_iff.mp (hnd.not_isMax_of_subset hclosed (F p.last) hlast)
  have hheight : (n : ℕ∞) ≤ height (F p.last) := by
    have hq := length_le_height_last (p := p.map F hstrict)
    rw [LTSeries.last_map] at hq
    exact hp ▸ hq
  have hstep : (n : ℕ∞) + 1 ≤ height Z := le_trans (by gcongr) (height_add_one_le hZ)
  rw [h]
  refine le_trans ?_ (height_le_krullDim Z)
  exact_mod_cast hstep

/-- A nowhere dense closed subset of a Noetherian space of finite dimension `m` has dimension
below `m`, provided the space has a point. -/
private theorem IsNowhereDense.exists_natCast_topologicalKrullDim_lt [NoetherianSpace X]
    {S : Set X} (hnd : IsNowhereDense S) (hclosed : IsClosed S)
    (hbot : topologicalKrullDim X ≠ ⊥) (hfin : topologicalKrullDim X ≠ ⊤) :
    ∃ m : ℕ, topologicalKrullDim X = m ∧ topologicalKrullDim S < m := by
  obtain ⟨m, hm⟩ := exists_natCast_of_ne_bot_of_ne_top hbot hfin
  exact ⟨m, hm, ENat.WithBot.add_one_le_natCast_iff.mp
    (hm ▸ hnd.topologicalKrullDim_add_one_le hclosed)⟩

/-- **A nowhere dense closed subset of a nonempty finite-dimensional Noetherian space has
strictly smaller dimension.** Both side conditions are needed: an empty `X` has an empty
nowhere dense closed subset of the same dimension `-∞`, and for `dim X = ∞` a nowhere dense
closed subset may again have dimension `∞`. -/
theorem IsNowhereDense.topologicalKrullDim_lt [NoetherianSpace X] {S : Set X}
    (hnd : IsNowhereDense S) (hclosed : IsClosed S) (hne : Nonempty X)
    (hfin : topologicalKrullDim X ≠ ⊤) :
    topologicalKrullDim S < topologicalKrullDim X := by
  have hbot : topologicalKrullDim X ≠ ⊥ := fun h =>
    (not_isEmpty_iff.mpr hne) ((topologicalKrullDim_eq_bot_iff_isEmpty X).mp h)
  obtain ⟨m, hm, hlt⟩ := hnd.exists_natCast_topologicalKrullDim_lt hclosed hbot hfin
  rwa [hm]

/-- **A nowhere dense closed subset of a Noetherian space of dimension at most `n + 1` has
dimension at most `n`.** This is the bounded form of `topologicalKrullDim_add_one_le`, and
unlike the strict forms it needs no side condition: the bound on `dim X` supplies the
finite-dimensionality, and an empty `S` satisfies the conclusion. -/
theorem IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ [NoetherianSpace X] {S : Set X}
    (hnd : IsNowhereDense S) (hclosed : IsClosed S) (n : ℕ)
    (hX : topologicalKrullDim X ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim S ≤ (n : WithBot ℕ∞) := by
  have h := le_trans (hnd.topologicalKrullDim_add_one_le hclosed) hX
  have h2 : topologicalKrullDim S < ((n + 1 : ℕ) : WithBot ℕ∞) :=
    ENat.WithBot.add_one_le_natCast_iff.mp h
  rw [show ((n + 1 : ℕ) : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞) + 1 by push_cast; rfl] at h2
  exact ENat.WithBot.lt_add_one_iff.mp h2

/-- **A nowhere dense closed subset of a Noetherian space of dimension at most one is
zero-dimensional.** The case of `IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ` that
the theory of curves uses. -/
theorem IsNowhereDense.topologicalKrullDim_nonpos_of_le_one [NoetherianSpace X] {S : Set X}
    (hnd : IsNowhereDense S) (hclosed : IsClosed S) (hX : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim S ≤ 0 := by
  have h := hnd.topologicalKrullDim_le_of_le_natCast_succ hclosed 0 (by simpa using hX)
  simpa using h

/-- **The strict dimension drop, read as natural numbers.** `fun x => (x.unbotD 0).toNat` is how
a descending induction reads `dim` as a natural number; the hypothesis that the ambient measure
is nonzero is what makes the reading faithful, and is exactly what such an induction has in its
inductive step. -/
theorem IsNowhereDense.toNat_unbotD_topologicalKrullDim_lt [NoetherianSpace X] {S : Set X}
    (hnd : IsNowhereDense S) (hclosed : IsClosed S) (hfin : topologicalKrullDim X ≠ ⊤)
    (hpos : ((topologicalKrullDim X).unbotD 0).toNat ≠ 0) :
    ((topologicalKrullDim S).unbotD 0).toNat < ((topologicalKrullDim X).unbotD 0).toNat := by
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    intro h
    rw [h] at hpos
    exact hpos (by simp)
  obtain ⟨m, hm, hlt⟩ := hnd.exists_natCast_topologicalKrullDim_lt hclosed hbot hfin
  have hX : ((topologicalKrullDim X).unbotD 0).toNat = m := by rw [hm]; simp
  rw [hX]
  rcases eq_or_ne (topologicalKrullDim S) ⊥ with h | hSbot
  · rw [h]
    simpa using Nat.pos_of_ne_zero (hX ▸ hpos)
  obtain ⟨j, hj⟩ := exists_natCast_of_ne_bot_of_ne_top hSbot (ne_top_of_lt hlt)
  rw [hj] at hlt ⊢
  have hcoe : ((j : ℕ∞) : WithBot ℕ∞) < ((m : ℕ∞) : WithBot ℕ∞) := hlt
  simpa using (by exact_mod_cast WithBot.coe_lt_coe.mp hcoe : j < m)

/-- **A subset that is closed in the ambient space and nowhere dense in a subspace containing
it has strictly smaller natural-number dimension than that subspace.** This is the relative
form, stated between two subsets of a common ambient space: it is
`IsNowhereDense.toNat_unbotD_topologicalKrullDim_lt` applied inside the subspace `Y`, with
`topologicalKrullDim_preimage_val` identifying the dimension of `A` read in `Y` with its
dimension read in `X`. -/
theorem toNat_unbotD_topologicalKrullDim_lt_of_isNowhereDense_subspace {Y A : Set X}
    [NoetherianSpace Y] (hA : A ⊆ Y) (hclosed : IsClosed A)
    (hnd : IsNowhereDense ((Subtype.val : Y → X) ⁻¹' A))
    (hfin : topologicalKrullDim Y ≠ ⊤)
    (hpos : ((topologicalKrullDim Y).unbotD 0).toNat ≠ 0) :
    ((topologicalKrullDim A).unbotD 0).toNat < ((topologicalKrullDim Y).unbotD 0).toNat := by
  rw [← topologicalKrullDim_preimage_val Y A hA]
  exact hnd.toNat_unbotD_topologicalKrullDim_lt (hclosed.preimage continuous_subtype_val) hfin hpos

/-- **Nowhere density inside a subspace, as a condition on that subspace's irreducible
components.** A nowhere-density hypothesis has an ambient space, and this is where the choice of
ambient space shows: `IsClosed.isNowhereDense_iff_forall_irreducibleComponents_not_subset`
applied inside the subspace `Y` asks `A` to miss every irreducible component **of `Y`**, which
is a strictly weaker family of sets than the irreducible components of `X`. In particular a set
nowhere dense in `X` need not be nowhere dense in a subspace `Y`: if `Y` is itself nowhere dense
in `X`, then `A = Y` satisfies the absolute hypothesis and fails the relative one outright. -/
theorem isNowhereDense_preimage_val_iff_forall_irreducibleComponents [NoetherianSpace X]
    {Y A : Set X} (hA : IsClosed A) :
    IsNowhereDense ((Subtype.val : Y → X) ⁻¹' A) ↔
      ∀ Z ∈ irreducibleComponents Y, ¬ (Subtype.val '' Z ⊆ A) := by
  have hpre : IsClosed ((Subtype.val : Y → X) ⁻¹' A) :=
    hA.preimage (continuous_subtype_val (p := fun x => x ∈ Y))
  rw [hpre.isNowhereDense_iff_forall_irreducibleComponents_not_subset]
  simp only [Set.image_subset_iff]

/-- **The subspace `Set.univ` has the dimension of the whole space.** With
`isNowhereDense_preimage_val_iff_forall_irreducibleComponents` this isolates the one case in
which absolute nowhere density is the relative one: for `Y = Set.univ` the subspace is
homeomorphic to the ambient space, so the two notions, and the two dimensions, agree. -/
theorem topologicalKrullDim_univ :
    topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
  (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
