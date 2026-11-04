module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 09YI: intersection of a constructible set with a constructible set

Let `X` be a topological space whose topology has a basis consisting of
quasi-compact open subsets (i.e. `PrespectralSpace X`). Let `E, E' ⊆ X`
be constructible subsets of `X`. Then the intersection `E ∩ E'`, viewed
as a subset of the topological subspace `E ⊆ X`, is constructible.

In Lean we phrase "`E ∩ E'` viewed inside `E`" as the preimage of `E'`
under the subtype inclusion `Subtype.val : E → X`; this preimage is the
canonical identification of `E ∩ E'` inside the subspace `E`.

The strategy follows the Stacks proof: combine the facts that

* every constructible set is retrocompact (Stacks 09YH); and
* if `T ⊆ X` is retrocompact and the topology of `X` has a basis of
  quasi-compact opens, then for every constructible set `E' ⊆ X` the
  intersection `E' ∩ T` is constructible in `T` (Stacks 09YF).

The second statement is proved by checking, via
`Topology.IsConstructible.preimage`, that for every retrocompact open
`V ⊆ X`, the preimage `(Subtype.val : T → X) ⁻¹' V` is retrocompact in
`T`. We verify this last fact by using the basis-of-quasi-compact-opens
hypothesis to write any compact open of `T` as `Subtype.val ⁻¹' W'` for
some quasi-compact open `W'` of `X`, and then applying the retrocompactness
of both `V` and `T`.

For "every constructible set is retrocompact" (with no extra hypothesis
on the ambient topology), we use the structural normal-form induction
principle `BooleanSubalgebra.closure_sdiff_sup_induction`: every
constructible set is a finite union of "differences" `U \ V` with `U, V`
retrocompact open. Such a difference `U \ V` is retrocompact because
`(U \ V) ∩ W = (U ∩ W) \ V` is a closed subset of the quasi-compact open
set `U ∩ W`. Unions of retrocompact sets are retrocompact, which closes
the induction.
-/

@[expose] public section

open Set Topology TopologicalSpace
open scoped Set.Notation

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The collection of retrocompact open subsets of `X` is a sublattice of `Set X`
(closed under finite unions and finite intersections) containing both `⊥` and `⊤`.
This is the auxiliary fact needed to invoke
`BooleanSubalgebra.closure_sdiff_sup_induction` on the generating set used to
define `Topology.IsConstructible`. -/
lemma isSublattice_isOpen_and_isRetrocompact :
    IsSublattice {U : Set X | IsOpen U ∧ IsRetrocompact U} :=
  ⟨fun _s hs _t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
   fun _s hs _t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩

/-- The empty set is a retrocompact open subset of `X`. -/
lemma bot_mem_isOpen_and_isRetrocompact :
    (⊥ : Set X) ∈ {U : Set X | IsOpen U ∧ IsRetrocompact U} :=
  ⟨isOpen_empty, .empty⟩

/-- The whole space is a retrocompact open subset of `X`. -/
lemma top_mem_isOpen_and_isRetrocompact :
    (⊤ : Set X) ∈ {U : Set X | IsOpen U ∧ IsRetrocompact U} :=
  ⟨isOpen_univ, .univ⟩

/-- The difference `U \ V` of two retrocompact open sets is retrocompact.

Intersecting with a quasi-compact open `W ⊆ X` gives
`(U \ V) ∩ W = (U ∩ W) \ V`, a closed subset of the quasi-compact set
`U ∩ W`. Closed subsets of quasi-compact sets are quasi-compact. -/
private lemma IsRetrocompact_sdiff_of_isOpen_isRetrocompact
    {U V : Set X} (hUcomp : IsRetrocompact U)
    (hVopen : IsOpen V) :
    IsRetrocompact (U \ V) := by
  intro W hWcomp hWopen
  -- `(U \ V) ∩ W = Vᶜ ∩ (U ∩ W)` is the intersection of the compact set `U ∩ W`
  -- with the closed set `Vᶜ`, hence quasi-compact.
  rw [show (U \ V) ∩ W = Vᶜ ∩ (U ∩ W) from by
    ext x; simp [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]; tauto]
  exact (hUcomp hWcomp hWopen).inter_left hVopen.isClosed_compl

/-- **Stacks 09YH.** Every constructible subset of a topological space is
retrocompact (no further hypothesis on `X`).

We use the normal-form induction principle on Boolean subalgebra closures:
every constructible set is a finite union of differences `U \ V` of two
retrocompact open sets, and both retrocompact-open differences and finite
unions of retrocompact sets are retrocompact. -/
@[ega "0 9.1.13" "special case",
  ega "0 9.1.4",
  ega "0 9.1.5" "partial",
  ega "IV 1.8.1" "partial",
  ega "IV 1.9.5" "(v), special case"]
theorem IsRetrocompact_of_IsConstructible
    {E : Set X} (hE : IsConstructible E) : IsRetrocompact E := by
  induction E, hE using BooleanSubalgebra.closure_sdiff_sup_induction
    (isSublattice := isSublattice_isOpen_and_isRetrocompact)
    (bot_mem := bot_mem_isOpen_and_isRetrocompact)
    (top_mem := top_mem_isOpen_and_isRetrocompact) with
  | sdiff U hU V hV => exact IsRetrocompact_sdiff_of_isOpen_isRetrocompact hU.2 hV.1
  | sup s _ t _ hs' ht' => exact hs'.union ht'

/-- Auxiliary: in a `PrespectralSpace`, every open subset of the subspace
topology on `T ⊆ X` whose underlying compact set is compact in `T` comes
from a quasi-compact open of `X`.

Concretely: if `W ⊆ T` is open in the subspace topology on `T` and compact,
then there exists a quasi-compact open `W' ⊆ X` of `X` such that
`W = (Subtype.val : T → X) ⁻¹' W'`. -/
private lemma exists_isCompact_isOpen_preimage_eq
    [PrespectralSpace X] {T : Set X} {W : Set T}
    (hWopen : IsOpen W) (hWcomp : IsCompact W) :
    ∃ W' : Set X, IsOpen W' ∧ IsCompact W' ∧
      W = (Subtype.val : T → X) ⁻¹' W' := by
  classical
  -- `W` is open in the subspace topology: there is `U` open in `X` with `W = val⁻¹' U`.
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.mp hWopen
  have hsubU : (Subtype.val : T → X) '' W ⊆ U := by
    rintro _ ⟨x, hxW, rfl⟩
    exact show x ∈ (Subtype.val : T → X) ⁻¹' U from hUeq ▸ hxW
  -- Every point of `val '' W` lies in a basic quasi-compact open contained in `U`,
  -- by the basis hypothesis.
  have hcover : (Subtype.val : T → X) '' W ⊆
      ⋃ V ∈ {V : Set X | IsOpen V ∧ IsCompact V ∧ V ⊆ U}, V := by
    intro x hx
    obtain ⟨V, ⟨hVopen, hVcomp⟩, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (hsubU hx) hUopen
    exact Set.mem_biUnion (show V ∈ _ from ⟨hVopen, hVcomp, hVU⟩) hxV
  -- Choose a finite subcover; its union is a quasi-compact open of `X`.
  obtain ⟨σ, hσsub, hσfin, hσcover⟩ :=
    (hWcomp.image continuous_subtype_val).elim_finite_subcover_image
      (b := {V : Set X | IsOpen V ∧ IsCompact V ∧ V ⊆ U}) (c := fun V ↦ V)
      (fun V hV ↦ hV.1) hcover
  refine ⟨⋃ V ∈ σ, V, isOpen_biUnion fun V hV ↦ (hσsub hV).1,
    hσfin.isCompact_biUnion fun V hV ↦ (hσsub hV).2.1, ?_⟩
  refine Set.eq_of_subset_of_subset (fun t htW ↦ hσcover ⟨t, htW, rfl⟩) fun t htU ↦ ?_
  rw [Set.mem_preimage, Set.mem_iUnion₂] at htU
  obtain ⟨V, hVσ, htV⟩ := htU
  simpa [hUeq] using show t ∈ (Subtype.val : T → X) ⁻¹' U from (hσsub hVσ).2.2 htV

/-- Auxiliary: for a retrocompact subset `T` of `X` and any retrocompact open
`V ⊆ X`, the preimage of `V` under `Subtype.val : T → X` is retrocompact in
the subspace topology of `T`. This is the key step of Stacks 09YF. -/
lemma isRetrocompact_preimage_subtypeVal
    [PrespectralSpace X] {T : Set X} (hT : IsRetrocompact T)
    {V : Set X} (hVopen : IsOpen V) (hVcomp : IsRetrocompact V) :
    IsRetrocompact ((Subtype.val : T → X) ⁻¹' V) := by
  intro W hWcomp hWopen
  obtain ⟨W', hW'open, hW'comp, hWeq⟩ :=
    exists_isCompact_isOpen_preimage_eq (T := T) hWopen hWcomp
  -- `(val ⁻¹' V) ∩ W = val ⁻¹' (V ∩ W')`
  rw [show ((Subtype.val : T → X) ⁻¹' V) ∩ W = (Subtype.val : T → X) ⁻¹' (V ∩ W') from by
    rw [hWeq]; ext t; simp [Set.mem_inter_iff, Set.mem_preimage]]
  -- The inclusion `val : T → X` is a topological embedding, so the preimage is compact
  -- iff its image `(V ∩ W') ∩ Set.range val = (V ∩ W') ∩ T` is; and `T ∩ (V ∩ W')` is
  -- quasi-compact since `V ∩ W'` is quasi-compact open and `T` is retrocompact.
  rw [(IsEmbedding.subtypeVal (p := (· ∈ T))).isCompact_iff,
    Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
  simpa [Set.inter_comm] using hT (hVcomp hW'comp hW'open) (hVopen.inter hW'open)

/-- **Stacks 09YI.** Let `X` be a topological space whose topology has a basis
of quasi-compact opens. For two constructible subsets `E, E'` of `X`, the
intersection `E ∩ E'` is constructible in `E` (i.e. its image as a subset of
the subspace `E ⊆ X`).

Equivalently in Lean: the preimage `(Subtype.val : E → X) ⁻¹' E'` is
constructible in the subspace topology of `E`. -/
@[stacks 09YI, ega "0 9.1.8" "partial", ega "0 9.2.1" "partial", sga "3 VIB 4.2" "partial"]
theorem isConstructible_preimage_subtypeVal_of_isConstructible
    [PrespectralSpace X] {E E' : Set X}
    (hE : IsConstructible E) (hE' : IsConstructible E') :
    IsConstructible ((Subtype.val : E → X) ⁻¹' E') :=
  -- `E` is retrocompact (Stacks 09YH), hence for every retrocompact open `V ⊆ X` the
  -- preimage `val⁻¹' V` is retrocompact in `E` (Stacks 09YF); conclude with
  -- `IsConstructible.preimage` for the continuous inclusion `val : E → X`.
  hE'.preimage continuous_subtype_val fun _V hVopen hVcomp ↦
    isRetrocompact_preimage_subtypeVal (IsRetrocompact_of_IsConstructible hE) hVopen hVcomp

