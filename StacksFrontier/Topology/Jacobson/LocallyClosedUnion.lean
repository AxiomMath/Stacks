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
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.Topology.Constructible.IrreducibleMeet
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite unions of locally closed subsets of a Jacobson space and of its closed points

Let `X` be a Jacobson topological space and let `X₀ = closedPoints X` carry the subspace
topology. The map `E ↦ E ∩ X₀`, that is, pullback along the inclusion `Subtype.val : X₀ → X`,
is a bijection between the finite unions of locally closed subsets of `X` and those of `X₀`.
It preserves inclusion in both directions and restricts to bijections on the locally closed,
the open, and the closed subsets.

## Main results

* `IsFiniteUnionLocallyClosed.inter`, `.union`, `.compl`, `.diff`: finite unions of
  locally closed subsets are stable under intersection, union, complement and set difference.
* `exists_isFiniteUnionLocallyClosed_preimage_eq`: every finite union of locally closed subsets
  of `closedPoints X` is the preimage of one in `X`.
* `IsFiniteUnionLocallyClosed.subset_iff_preimage_subset` and
  `IsFiniteUnionLocallyClosed.eq_iff_preimage_eq`: inclusion and equality of such
  subsets of a Jacobson space are detected on the closed points.
* `jacobsonSpace_locallyClosed_bijection`: the bijection itself, together with its four
  compatibility properties.
-/

@[expose] public section

open Set Topology

section helper_lemmas

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every open subset of `closedPoints X` lifts to an open subset of `X` with the same preimage. -/
lemma exists_isOpen_preimage_eq (S : Set (closedPoints X)) (hS : IsOpen S) :
    ∃ U : Set X, IsOpen U ∧ Subtype.val ⁻¹' U = S :=
  isOpen_induced_iff.mp hS

/-- Every closed subset of `closedPoints X` lifts to a closed subset of `X` with the same
preimage. -/
lemma exists_isClosed_preimage_eq (S : Set (closedPoints X)) (hS : IsClosed S) :
    ∃ F : Set X, IsClosed F ∧ Subtype.val ⁻¹' F = S :=
  isClosed_induced_iff.mp hS

/-- The preimage of a finite union of locally closed subsets under a continuous map is again a
finite union of locally closed subsets. -/
@[ega "IV 10.1.1" "partial"]
lemma IsFiniteUnionLocallyClosed.preimage {f : Y → X} (hf : Continuous f)
    {s : Set X} (hs : IsFiniteUnionLocallyClosed s) :
    IsFiniteUnionLocallyClosed (f ⁻¹' s) := by
  obtain ⟨n, E, hE, rfl⟩ := hs
  exact ⟨n, fun i => f ⁻¹' E i, fun i => (hE i).preimage hf, by simp [preimage_iUnion]⟩

/-- Any locally closed subset is a finite union (singleton) of locally closed subsets. -/
lemma IsLocallyClosed.isFiniteUnionLocallyClosed {s : Set Y} (hs : IsLocallyClosed s) :
    IsFiniteUnionLocallyClosed s :=
  ⟨1, fun _ => s, fun _ => hs, by ext; simp⟩

/-- Open subsets are finite unions of locally closed. -/
lemma IsOpen.isFiniteUnionLocallyClosed {s : Set Y} (hs : IsOpen s) :
    IsFiniteUnionLocallyClosed s :=
  IsLocallyClosed.isFiniteUnionLocallyClosed hs.isLocallyClosed

/-- Closed subsets are finite unions of locally closed. -/
lemma IsClosed.isFiniteUnionLocallyClosed {s : Set Y} (hs : IsClosed s) :
    IsFiniteUnionLocallyClosed s :=
  IsLocallyClosed.isFiniteUnionLocallyClosed hs.isLocallyClosed

/-- Every locally closed subset of `closedPoints X` lifts to a locally closed subset of `X`
with the same preimage. -/
lemma exists_isLocallyClosed_preimage_eq (S : Set (closedPoints X)) (hS : IsLocallyClosed S) :
    ∃ E : Set X, IsLocallyClosed E ∧ Subtype.val ⁻¹' E = S := by
  obtain ⟨Us, Fs, hUs, hFs, rfl⟩ := hS
  obtain ⟨U, hU, rfl⟩ := exists_isOpen_preimage_eq Us hUs
  obtain ⟨F, hF, rfl⟩ := exists_isClosed_preimage_eq Fs hFs
  exact ⟨U ∩ F, hU.isLocallyClosed.inter hF.isLocallyClosed, rfl⟩

/-- Every finite union of locally closed subsets of `closedPoints X` lifts to a finite union
of locally closed subsets of `X` with the same preimage. -/
@[ega "IV 10.4.10" "partial"]
lemma exists_isFiniteUnionLocallyClosed_preimage_eq
    (S : Set (closedPoints X)) (hS : IsFiniteUnionLocallyClosed S) :
    ∃ E : Set X, IsFiniteUnionLocallyClosed E ∧ Subtype.val ⁻¹' E = S := by
  obtain ⟨n, F, hF_lc, rfl⟩ := hS
  choose E hE_lc hE_preim using fun i => exists_isLocallyClosed_preimage_eq (F i) (hF_lc i)
  exact ⟨⋃ i, E i, ⟨n, E, hE_lc, rfl⟩, by rw [preimage_iUnion]; exact iUnion_congr hE_preim⟩

/-- The complement of a locally closed set is a finite union of locally closed sets
(namely, the complement of the open part union the complement of the closed part). -/
lemma IsLocallyClosed.compl_isFiniteUnionLocallyClosed {s : Set X} (hs : IsLocallyClosed s) :
    IsFiniteUnionLocallyClosed sᶜ := by
  obtain ⟨U, F, hU, hF, rfl⟩ := hs
  refine ⟨2, ![Uᶜ, Fᶜ], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hU.isClosed_compl.isLocallyClosed
    · exact hF.isOpen_compl.isLocallyClosed
  · rw [compl_inter]
    ext x
    simp [Fin.exists_fin_succ]

/-- The intersection of two finite-union-locally-closed sets is again a finite union
of locally closed sets. -/
lemma IsFiniteUnionLocallyClosed.inter {s t : Set X}
    (hs : IsFiniteUnionLocallyClosed s) (ht : IsFiniteUnionLocallyClosed t) :
    IsFiniteUnionLocallyClosed (s ∩ t) := by
  obtain ⟨n, E, hE, rfl⟩ := hs
  obtain ⟨m, F, hF, rfl⟩ := ht
  refine ⟨n * m, fun k => E (finProdFinEquiv.symm k).1 ∩ F (finProdFinEquiv.symm k).2,
    fun k => (hE _).inter (hF _), ?_⟩
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  refine ⟨fun ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ => ⟨finProdFinEquiv (i, j), by simp [hi, hj]⟩, ?_⟩
  rintro ⟨k, hk⟩
  exact ⟨⟨_, hk.1⟩, ⟨_, hk.2⟩⟩

/-- The union of two finite-union-locally-closed sets is again a finite union of locally closed
sets. -/
lemma IsFiniteUnionLocallyClosed.union {s t : Set X}
    (hs : IsFiniteUnionLocallyClosed s) (ht : IsFiniteUnionLocallyClosed t) :
    IsFiniteUnionLocallyClosed (s ∪ t) := by
  obtain ⟨n, E, hE, rfl⟩ := hs
  obtain ⟨m, F, hF, rfl⟩ := ht
  refine ⟨n + m, Sum.elim E F ∘ finSumFinEquiv.symm, ?_, ?_⟩
  · intro k
    simp only [Function.comp_apply]
    rcases finSumFinEquiv.symm k with i | j
    · exact hE i
    · exact hF j
  · ext x
    simp only [mem_union, mem_iUnion, Function.comp_apply]
    refine ⟨fun h => ?_, fun ⟨k, hk⟩ => ?_⟩
    · rcases h with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact ⟨finSumFinEquiv (Sum.inl i), by simp [hi]⟩
      · exact ⟨finSumFinEquiv (Sum.inr j), by simp [hj]⟩
    · rcases h : finSumFinEquiv.symm k with i | j
      · exact Or.inl ⟨i, by rw [h] at hk; simpa using hk⟩
      · exact Or.inr ⟨j, by rw [h] at hk; simpa using hk⟩

/-- The complement of a union `⋃ i : Fin n, E i` of locally closed sets is again a finite
union of locally closed sets. -/
private lemma compl_iUnion_fin_isFiniteUnionLocallyClosed :
    ∀ (n : ℕ) (E : Fin n → Set X), (∀ i, IsLocallyClosed (E i)) →
      IsFiniteUnionLocallyClosed (⋃ i, E i)ᶜ
  | 0, E, _ => by
    rw [show (⋃ i, E i) = (∅ : Set X) by simp [iUnion_of_empty], compl_empty]
    exact IsClosed.isFiniteUnionLocallyClosed isClosed_univ
  | n + 1, E, hE => by
    rw [show (⋃ i, E i) = E 0 ∪ (⋃ i : Fin n, E i.succ) by
          ext x; simp [Fin.exists_fin_succ], compl_union]
    exact (IsLocallyClosed.compl_isFiniteUnionLocallyClosed (hE 0)).inter
      (compl_iUnion_fin_isFiniteUnionLocallyClosed n (fun i => E i.succ) (fun i => hE i.succ))

/-- The complement of a finite union of locally closed sets is a finite union of locally
closed sets. -/
lemma IsFiniteUnionLocallyClosed.compl {s : Set X} (hs : IsFiniteUnionLocallyClosed s) :
    IsFiniteUnionLocallyClosed sᶜ := by
  obtain ⟨n, E, hE, rfl⟩ := hs
  exact compl_iUnion_fin_isFiniteUnionLocallyClosed n E hE

/-- The set difference of two finite-union-locally-closed sets is a finite union
of locally closed sets. -/
lemma IsFiniteUnionLocallyClosed.diff {s t : Set X}
    (hs : IsFiniteUnionLocallyClosed s) (ht : IsFiniteUnionLocallyClosed t) :
    IsFiniteUnionLocallyClosed (s \ t) := by
  rw [Set.sdiff_eq]
  exact hs.inter ht.compl

variable [JacobsonSpace X]

/-- In a Jacobson space, every non-empty finite-union-of-locally-closed subset meets
`closedPoints X`. -/
@[ega "IV 10.1.2" "partial"]
lemma IsFiniteUnionLocallyClosed.nonempty_inter_closedPoints {s : Set X}
    (hs : IsFiniteUnionLocallyClosed s) (h : s.Nonempty) :
    (s ∩ closedPoints X).Nonempty := by
  obtain ⟨n, E, hE, rfl⟩ := hs
  obtain ⟨x, hx⟩ := h
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  obtain ⟨y, hyEi, hyC⟩ := _root_.nonempty_inter_closedPoints ⟨x, hxi⟩ (hE i)
  exact ⟨y, mem_iUnion.mpr ⟨i, hyEi⟩, hyC⟩

/-- In a Jacobson space, `s ⊆ t` if and only if the preimage of `s` along the inclusion of
`closedPoints X` is contained in that of `t`. -/
lemma IsFiniteUnionLocallyClosed.subset_iff_preimage_subset {s t : Set X}
    (hs : IsFiniteUnionLocallyClosed s) (ht : IsFiniteUnionLocallyClosed t) :
    s ⊆ t ↔ (Subtype.val : closedPoints X → X) ⁻¹' s ⊆ Subtype.val ⁻¹' t := by
  refine ⟨preimage_mono, fun h => ?_⟩
  by_contra hst
  rw [Set.not_subset] at hst
  obtain ⟨x, hxs, hxt⟩ := hst
  obtain ⟨y, ⟨hys, hyt⟩, hyC⟩ :=
    (hs.diff ht).nonempty_inter_closedPoints ⟨x, hxs, hxt⟩
  exact hyt (h (show (⟨y, hyC⟩ : closedPoints X) ∈ Subtype.val ⁻¹' s from hys))

/-- Equality version: two finite-union-of-locally-closed subsets are equal iff their
preimages along the inclusion of `closedPoints X` are equal. -/
lemma IsFiniteUnionLocallyClosed.eq_iff_preimage_eq {s t : Set X}
    (hs : IsFiniteUnionLocallyClosed s) (ht : IsFiniteUnionLocallyClosed t) :
    s = t ↔ (Subtype.val : closedPoints X → X) ⁻¹' s = Subtype.val ⁻¹' t :=
  ⟨fun h => h ▸ rfl, fun hpre => Subset.antisymm
    ((hs.subset_iff_preimage_subset ht).mpr hpre.le)
    ((ht.subset_iff_preimage_subset hs).mpr hpre.ge)⟩

end helper_lemmas

/-- **Stacks 005Z**. Let `X` be a Jacobson topological space, and let `X₀ = closedPoints X`
carry the subspace topology. There exists a bijection `Φ` between the finite unions of locally
closed subsets of `X` and of `X₀`, given by pullback `E ↦ Subtype.val ⁻¹' E`, that is,
`E ↦ E ∩ X₀`, which preserves inclusion in both directions and restricts to bijections on the
locally closed, the open, and the closed subsets. -/
@[stacks 005Z,
  ega "IV 10.1.2" "a′ ⇒ c and c′, a′ ⇒ c″",
  ega "IV 10.2.7" "special case",
  ega "IV 10.3.1" "Forward direction",
  ega "IV 10.9.1" "more general",
  ega "IV 10.9.2" "partial"]
theorem jacobsonSpace_locallyClosed_bijection
    (X : Type*) [TopologicalSpace X] [JacobsonSpace X] :
    ∃ Φ : {s : Set X // IsFiniteUnionLocallyClosed s} ≃
          {s : Set ↥(closedPoints X) // IsFiniteUnionLocallyClosed s},
      (∀ E, (Φ E).1 = Subtype.val ⁻¹' E.1) ∧
      (∀ E E', E.1 ⊆ E'.1 ↔ (Φ E).1 ⊆ (Φ E').1) ∧
      (∀ E, IsLocallyClosed E.1 ↔ IsLocallyClosed (Φ E).1) ∧
      (∀ E, IsOpen E.1 ↔ IsOpen (Φ E).1) ∧
      (∀ E, IsClosed E.1 ↔ IsClosed (Φ E).1) := by
  have hbij : Function.Bijective
      (fun E : {s : Set X // IsFiniteUnionLocallyClosed s} =>
        (⟨Subtype.val ⁻¹' E.1, E.2.preimage continuous_subtype_val⟩ :
          {s : Set ↥(closedPoints X) // IsFiniteUnionLocallyClosed s})) :=
    ⟨fun E E' h => Subtype.ext ((E.2.eq_iff_preimage_eq E'.2).mpr (congrArg Subtype.val h)),
     fun S => (exists_isFiniteUnionLocallyClosed_preimage_eq S.1 S.2).elim
       fun E hE => ⟨⟨E, hE.1⟩, Subtype.ext hE.2⟩⟩
  refine ⟨Equiv.ofBijective _ hbij, fun _ => rfl,
    fun E E' => E.2.subset_iff_preimage_subset E'.2, ?_, ?_, ?_⟩
  all_goals
    intro E
    refine ⟨fun h => h.preimage continuous_subtype_val, fun h => ?_⟩
  · obtain ⟨E', hE', hpre⟩ := exists_isLocallyClosed_preimage_eq _ h
    exact (E.2.eq_iff_preimage_eq hE'.isFiniteUnionLocallyClosed).mpr hpre.symm ▸ hE'
  · obtain ⟨U, hU, hpre⟩ := exists_isOpen_preimage_eq _ h
    exact (E.2.eq_iff_preimage_eq hU.isFiniteUnionLocallyClosed).mpr hpre.symm ▸ hU
  · obtain ⟨F, hF, hpre⟩ := exists_isClosed_preimage_eq _ h
    exact (E.2.eq_iff_preimage_eq hF.isFiniteUnionLocallyClosed).mpr hpre.symm ▸ hF
