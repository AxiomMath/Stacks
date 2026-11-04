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
public import StacksFrontier.Topology.Constructible.IrreducibleMeet
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Jacobson property passes to subspaces

Let `X` be a Jacobson topological space and let `T ⊆ X` carry the subspace topology. For each
of the kinds of subset treated here — open, closed, locally closed, an arbitrary union of
locally closed subsets, a finite union of locally closed subsets, and a subset that locally on
`X` is a union of locally closed subsets — the space `T` is again Jacobson and every point of
`T` that is closed in `T` is closed in `X`.

## Main definitions

* `IsLocallyUnionOfLocallyClosed`: a subset whose intersection with each member of some open
  cover of `X` is a union of subsets locally closed in that member.
* `StarProperty`: every nonempty locally closed subset of the subspace `T` contains a point
  that is closed in `X`.

## Main results

* `jacobson_of_starProperty`: a subset with `StarProperty` is Jacobson, and its closed points
  are closed in `X`.
* `starProperty_of_iUnion_isLocallyClosed`: a union of locally closed subsets of a Jacobson
  space has `StarProperty`.
* `jacobson_of_iUnion_isLocallyClosed`, `jacobson_of_isLocallyClosed`, `jacobson_of_isOpen`,
  `jacobson_of_isClosed`, `jacobson_of_isFiniteUnionLocallyClosed`,
  `jacobson_of_isLocallyUnionOfLocallyClosed`: the conclusion for a union of locally closed
  subsets, a locally closed subset, an open subset, a closed subset, a finite union of locally
  closed subsets, and a subset that is locally a union of locally closed subsets.
-/

@[expose] public section

universe u v

/-- A subset `T ⊆ X` *locally on `X` is a union of locally closed subsets* if
there exists an open cover `X = ⋃ α, U α` such that for every `α`, the
intersection `T ∩ U α` can be written as a union of subsets that are locally
closed in `U α`. -/
def IsLocallyUnionOfLocallyClosed {X : Type u} [TopologicalSpace X] (T : Set X) : Prop :=
  ∃ (α : Type u) (U : α → Set X),
    (∀ a, IsOpen (U a)) ∧ (⋃ a, U a) = Set.univ ∧
    ∀ a, ∃ (ι : Type u) (L : ι → Set (U a)),
      (∀ i, IsLocallyClosed (L i)) ∧
      (Subtype.val ⁻¹' T : Set (U a)) = ⋃ i, L i

/-- Property `(*)`: every nonempty locally closed subset of `T` (with respect
to the subspace topology on `T`) contains a point that is closed in `X`. -/
def StarProperty {X : Type u} [TopologicalSpace X] (T : Set X) : Prop :=
  ∀ (A : Set T), A.Nonempty → IsLocallyClosed A →
    (Subtype.val '' A ∩ closedPoints X).Nonempty

/-- Closed points of `X` that lie in `T` are also closed in `T` (in the
subspace topology). -/
lemma closedPoint_in_T_of_closedPoint_in_X
    {X : Type u} [TopologicalSpace X] {T : Set X}
    (t : T) (ht : (t : X) ∈ closedPoints X) : t ∈ closedPoints T := by
  have h₁ : IsClosed ({(t : X)} : Set X) := by
    simpa [Set.mem_singleton_iff] using ht
  have hpre : ({t} : Set T) = (Subtype.val : T → X) ⁻¹' ({(t : X)} : Set X) := by
    ext t'
    simp [Subtype.ext_iff]
  have h₂ : IsClosed ({t} : Set T) := by
    rw [hpre]
    exact h₁.preimage continuous_subtype_val
  simpa [Set.mem_singleton_iff] using h₂

/-- The image of `{t} ⊆ T` under `Subtype.val : T → X` is `{(t : X)}`. -/
lemma image_singleton_val {X : Type u} {T : Set X} (t : T) :
    (Subtype.val '' ({t} : Set T) : Set X) = {(t : X)} := by
  ext x
  simp

/-- Image of a locally closed subset of an open subspace `U ⊆ X` (under the
inclusion `U → X`) is locally closed in `X`. -/
@[ega "IV 10.4.5.1" "special case"]
lemma isLocallyClosed_image_subtypeVal_of_isOpen
    {X : Type u} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {L : Set U} (hL : IsLocallyClosed L) :
    IsLocallyClosed (Subtype.val '' L : Set X) := by
  have hRange : IsLocallyClosed (Set.range (Subtype.val : U → X)) := by
    rw [Subtype.range_val]
    exact hU.isLocallyClosed
  exact hL.image Topology.IsInducing.subtypeVal hRange

/-- If `T ⊆ X` satisfies `StarProperty`, then `T` is Jacobson and its closed points are
closed in `X`. -/
theorem jacobson_of_starProperty
    {X : Type u} [TopologicalSpace X] {T : Set X} (hT : StarProperty T) :
    JacobsonSpace T ∧ (closedPoints T ⊆ Subtype.val ⁻¹' closedPoints X) := by
  refine ⟨?_, ?_⟩
  · -- Jacobson: every nonempty locally closed subset of `T` meets `closedPoints T`.
    rw [jacobsonSpace_iff_locallyClosed]
    intro A hAne hAlc
    obtain ⟨x, hxA, hxX⟩ := hT A hAne hAlc
    rcases hxA with ⟨a, haA, rfl⟩
    refine ⟨a, haA, ?_⟩
    exact closedPoint_in_T_of_closedPoint_in_X a hxX
  · -- Closed points of `T` are closed in `X`.
    intro t ht
    have hSing : ({t} : Set T).Nonempty := ⟨t, rfl⟩
    have hClosed : IsClosed ({t} : Set T) := by
      simpa [Set.mem_singleton_iff] using ht
    have hLC : IsLocallyClosed ({t} : Set T) := hClosed.isLocallyClosed
    obtain ⟨x, hxIm, hxX⟩ := hT ({t} : Set T) hSing hLC
    rw [image_singleton_val] at hxIm
    rcases hxIm with rfl
    exact hxX

/-- If `X` is Jacobson and `T = ⋃ i, L i` is a union of locally closed subsets of `X`, then
`T` satisfies `StarProperty`. -/
theorem starProperty_of_iUnion_isLocallyClosed
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {ι : Type v} {L : ι → Set X} (hL : ∀ i, IsLocallyClosed (L i)) :
    StarProperty (⋃ i, L i : Set X) := by
  intro A hAne hAlc
  -- `Subtype.val : ↥(⋃ i, L i) → X` is inducing.
  have hInd : Topology.IsInducing (Subtype.val : (⋃ i, L i : Set X) → X) :=
    Topology.IsInducing.subtypeVal
  -- So `A = Subtype.val ⁻¹' E` for some `E ⊆ X` locally closed in `X`.
  obtain ⟨E, hEloc, hEpre⟩ := hInd.isLocallyClosed_iff.mp hAlc
  -- Pick a point `a ∈ A`; it lies in `L i` for some `i`.
  obtain ⟨a, haA⟩ := hAne
  have haTX : (a : X) ∈ (⋃ i, L i : Set X) := a.2
  rw [Set.mem_iUnion] at haTX
  obtain ⟨i, haLi⟩ := haTX
  -- `(a : X) ∈ E` since `a ∈ Subtype.val ⁻¹' E`.
  have haE : (a : X) ∈ E := by
    have : a ∈ (Subtype.val ⁻¹' E : Set (⋃ i, L i : Set X)) := by
      rw [hEpre]; exact haA
    simpa using this
  -- `E ∩ L i` is nonempty and locally closed in `X`.
  have hELne : (E ∩ L i).Nonempty := ⟨(a : X), haE, haLi⟩
  have hELlc : IsLocallyClosed (E ∩ L i) := hEloc.inter (hL i)
  -- By Jacobson, `E ∩ L i` meets `closedPoints X`.
  obtain ⟨y, ⟨hyE, hyLi⟩, hyX⟩ := nonempty_inter_closedPoints hELne hELlc
  -- Build `y` as a point of `T = ⋃ i, L i`.
  have hyT : y ∈ (⋃ i, L i : Set X) := Set.mem_iUnion.mpr ⟨i, hyLi⟩
  refine ⟨y, ⟨⟨y, hyT⟩, ?_, rfl⟩, hyX⟩
  -- Show `⟨y, hyT⟩ ∈ A`, i.e. `y ∈ E`.
  have : (⟨y, hyT⟩ : (⋃ i, L i : Set X)) ∈ (Subtype.val ⁻¹' E : Set _) := hyE
  rw [hEpre] at this
  exact this

/-- **Stacks 005X**. A (possibly infinite) union of locally closed subsets of a Jacobson space
is Jacobson, and its closed points are closed in the ambient space. -/
@[stacks 005X, ega "IV 10.3.2", ega "IV 10.3.3" "necessity", ega "IV 10.4.3" "more general"]
theorem jacobson_of_iUnion_isLocallyClosed
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {ι : Type v} {L : ι → Set X} (hL : ∀ i, IsLocallyClosed (L i)) :
    JacobsonSpace (⋃ i, L i : Set X) ∧
      (closedPoints (⋃ i, L i : Set X) ⊆ Subtype.val ⁻¹' closedPoints X) :=
  jacobson_of_starProperty (starProperty_of_iUnion_isLocallyClosed hL)

/-- **Stacks 005X**. A locally closed subset of a Jacobson space is Jacobson, and its closed
points are closed in the ambient space. -/
@[stacks 005X,
  ega "IV 10.3.2" "locally closed case",
  ega "IV 10.3.3" "necessity",
  ega "IV 10.4.3" "more general",
  ega "IV 10.4.7" "special case",
  ega "IV 10.9.2" "special case"]
theorem jacobson_of_isLocallyClosed
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {T : Set X} (hT : IsLocallyClosed T) :
    JacobsonSpace T ∧ (closedPoints T ⊆ Subtype.val ⁻¹' closedPoints X) := by
  -- View `T` as a `Unit`-indexed union of locally closed sets and apply Case 4.
  have h := jacobson_of_iUnion_isLocallyClosed
    (X := X) (ι := PUnit.{u+1}) (L := fun _ => T) (fun _ => hT)
  have hEq : (⋃ _ : PUnit.{u+1}, T) = T := Set.iUnion_const T
  rw [hEq] at h
  exact h

/-- **Stacks 005X**. An open subset of a Jacobson space is Jacobson, and its closed points are
closed in the ambient space. -/
@[stacks 005X,
  ega "IV 10.3.2" "special case",
  ega "IV 10.3.3" "necessity",
  ega "IV 10.4.3" "Open subpreschemes",
  ega "IV 10.9.2" "special case"]
theorem jacobson_of_isOpen
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {T : Set X} (hT : IsOpen T) :
    JacobsonSpace T ∧ (closedPoints T ⊆ Subtype.val ⁻¹' closedPoints X) :=
  jacobson_of_isLocallyClosed hT.isLocallyClosed

/-- **Stacks 005X**. A closed subset of a Jacobson space is Jacobson, and its closed points are
closed in the ambient space. -/
@[stacks 005X,
  ega "IV 10.3.2" "closed subspace case",
  ega "IV 10.4.3" "Closed subpreschemes",
  ega "IV 10.4.7" "closed subschemes"]
theorem jacobson_of_isClosed
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {T : Set X} (hT : IsClosed T) :
    JacobsonSpace T ∧ (closedPoints T ⊆ Subtype.val ⁻¹' closedPoints X) :=
  jacobson_of_isLocallyClosed hT.isLocallyClosed

/-- **Stacks 005X**. A finite union of locally closed subsets of a Jacobson space is Jacobson,
and its closed points are closed in the ambient space. -/
@[stacks 005X, ega "IV 10.3.2" "special case"]
theorem jacobson_of_isFiniteUnionLocallyClosed
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {T : Set X} (hT : IsFiniteUnionLocallyClosed T) :
    JacobsonSpace T ∧ (closedPoints T ⊆ Subtype.val ⁻¹' closedPoints X) := by
  obtain ⟨n, L, hLloc, hUnion⟩ := hT
  rw [hUnion]
  exact jacobson_of_iUnion_isLocallyClosed hLloc

/-- **Stacks 005X**. A subset of a Jacobson space which locally on `X` is a union of locally
closed subsets is Jacobson, and its closed points are closed in the ambient space. -/
@[stacks 005X,
  ega "IV 10.3.2" "more general",
  ega "IV 10.3.3" "necessity",
  ega "IV 10.4.3" "more general",
  ega "IV 10.4.7" "special case"]
theorem jacobson_of_isLocallyUnionOfLocallyClosed
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {T : Set X} (hT : IsLocallyUnionOfLocallyClosed T) :
    JacobsonSpace T ∧ (closedPoints T ⊆ Subtype.val ⁻¹' closedPoints X) := by
  obtain ⟨α, U, hUopen, hUcover, hLocal⟩ := hT
  -- Choose, for each `α`, the index type `ι` and family `L` of locally closed sets.
  choose ι L hLloc hLunion using hLocal
  -- Express `T` as a union of locally closed subsets of `X`:
  -- `T = ⋃ (p : Σ a, ι a), Subtype.val '' (L p.1 p.2)`.
  have hTunion : T = ⋃ (p : Σ a, ι a),
      (Subtype.val '' (L p.1 p.2) : Set X) := by
    apply Set.eq_of_subset_of_subset
    · intro x hxT
      have hxU : x ∈ (⋃ a, U a) := by rw [hUcover]; trivial
      rw [Set.mem_iUnion] at hxU
      obtain ⟨a, hxUa⟩ := hxU
      have hxpre : (⟨x, hxUa⟩ : U a) ∈ (Subtype.val ⁻¹' T : Set (U a)) := hxT
      rw [hLunion a, Set.mem_iUnion] at hxpre
      obtain ⟨i, hxLai⟩ := hxpre
      refine Set.mem_iUnion.mpr ⟨⟨a, i⟩, ?_⟩
      exact ⟨⟨x, hxUa⟩, hxLai, rfl⟩
    · intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨⟨a, i⟩, hxImg⟩ := hx
      rcases hxImg with ⟨y, hyL, rfl⟩
      have hyT : (y : X) ∈ (Subtype.val '' (Subtype.val ⁻¹' T : Set (U a)) : Set X) := by
        rw [hLunion a]
        exact ⟨y, Set.mem_iUnion.mpr ⟨i, hyL⟩, rfl⟩
      rcases hyT with ⟨z, hzT, hzy⟩
      have : (y : X) = (z : X) := hzy.symm
      rw [this]
      exact hzT
  -- Each piece is locally closed in `X`.
  have hMloc : ∀ p : Σ a, ι a,
      IsLocallyClosed (Subtype.val '' (L p.1 p.2) : Set X) :=
    fun p => isLocallyClosed_image_subtypeVal_of_isOpen (hUopen p.1) (hLloc p.1 p.2)
  -- Apply Case 4.
  rw [hTunion]
  exact jacobson_of_iUnion_isLocallyClosed hMloc

