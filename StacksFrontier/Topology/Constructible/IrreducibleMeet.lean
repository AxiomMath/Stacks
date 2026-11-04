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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite unions of locally closed subsets meeting an irreducible set

For an irreducible subset `Z` of a topological space `X` and a subset `E` that is a finite
union of locally closed subsets, the intersection `E ∩ Z` contains an open dense subset of
`Z` exactly when it is dense in `Z`, and — if `Z` has a generic point `ξ` — exactly when
`ξ ∈ E`.

## Main definitions

* `IsFiniteUnionLocallyClosed`: a subset is a union of finitely many locally closed subsets.
* `IsOpenDenseSubsetOf`: a subset of `Z` that is open in the subspace topology of `Z` and
  dense in `Z`.

## Main results

* `irreducible_subset_finite_iUnion_closed`: an irreducible set contained in a finite union
  of closed sets is contained in one of them.
* `irreducible_subset_closure_open_inter`: for irreducible `Z` and open `U` with `U ∩ Z`
  nonempty, `Z ⊆ closure (U ∩ Z)`.
* `open_dense_iff_dense`: `E ∩ Z` contains an open dense subset of `Z` iff it is dense in `Z`.
* `tfae_with_generic_point`: for `Z` with generic point `ξ`, the two conditions above are
  also equivalent to `ξ ∈ E`.
-/

@[expose] public section

open Set Topology


variable {X : Type*} [TopologicalSpace X]

/-- A subset `E ⊆ X` is a finite union of locally closed subsets if there exist
finitely many locally closed subsets `L₀, …, L_{n-1}` of `X` whose union is `E`. -/
@[ega "IV 10.1.1"]
def IsFiniteUnionLocallyClosed (E : Set X) : Prop :=
  ∃ (n : ℕ) (L : Fin n → Set X), (∀ i, IsLocallyClosed (L i)) ∧ E = ⋃ i, L i

/-- A subset `V ⊆ Z` is an *open dense subset of `Z`* if it is open in the
subspace topology of `Z` (equivalently, `V = U ∩ Z` for some open `U ⊆ X`) and
dense in `Z` (equivalently, `Z ⊆ closure V`, closure taken in `X`). -/
def IsOpenDenseSubsetOf (V Z : Set X) : Prop :=
  V ⊆ Z ∧ (∃ U : Set X, IsOpen U ∧ V = U ∩ Z) ∧ Z ⊆ closure V

/-- An irreducible subset contained in a finite union of closed sets is
contained in one of them. -/
@[ega "0 2.1.7" "more general"]
lemma irreducible_subset_finite_iUnion_closed
    {Y : Type*} [TopologicalSpace Y] {Z : Set Y} (hZ : IsIrreducible Z)
    {n : ℕ} (F : Fin n → Set Y) (hF : ∀ i, IsClosed (F i))
    (hsub : Z ⊆ ⋃ i, F i) :
    ∃ i, Z ⊆ F i := by
  classical
  let t : Finset (Set Y) := Finset.univ.image F
  obtain ⟨z, hz, hZz⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ t
    (by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_univ, true_and, t] at hz
      obtain ⟨i, rfl⟩ := hz
      exact hF i)
    (fun x hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub hx)
      exact ⟨F i, by simp [t], hi⟩)
  simp only [Finset.mem_image, Finset.mem_univ, true_and, t] at hz
  obtain ⟨i, rfl⟩ := hz
  exact ⟨i, hZz⟩

/-- For an irreducible set `Z` and an open set `U` such that `U ∩ Z` is nonempty,
`Z ⊆ closure (U ∩ Z)`. -/
@[ega "0 2.1.1" "open-density criterion", ega "0 2.1.6" "density", sga "3 VIB 4.2" "partial"]
lemma irreducible_subset_closure_open_inter
    {Y : Type*} [TopologicalSpace Y] {Z : Set Y} (hZ : IsIrreducible Z)
    {U : Set Y} (hU : IsOpen U) (hne : (U ∩ Z).Nonempty) :
    Z ⊆ closure (U ∩ Z) := by
  intro z hz
  rw [mem_closure_iff]
  intro O hO hzO
  obtain ⟨w, hwZ, hwO, hwU⟩ :=
    hZ.2 O U hO hU ⟨z, hz, hzO⟩ (by rw [Set.inter_comm]; exact hne)
  exact ⟨w, hwO, hwU, hwZ⟩

/-- If `E ∩ Z` is dense in an irreducible `Z` and `E` is a finite union of locally closed sets,
then some piece `U ∩ C` of `E` has `Z ⊆ C` and `U` meeting `Z`. -/
private theorem exists_open_closed_of_dense
    {Z : Set X} (hZ : IsIrreducible Z) {E : Set X} (hE : IsFiniteUnionLocallyClosed E)
    (h : Z ⊆ closure (E ∩ Z)) :
    ∃ U C : Set X, IsOpen U ∧ IsClosed C ∧ Z ⊆ C ∧ (U ∩ Z).Nonempty ∧ U ∩ C ⊆ E := by
  obtain ⟨n, L, hL, hEeq⟩ := hE
  choose U C hU hC hLi using hL
  have hZsub : Z ⊆ ⋃ i, closure (U i ∩ C i ∩ Z) := by
    refine h.trans (closure_minimal ?_ (isClosed_iUnion_of_finite fun _ => isClosed_closure))
    rw [hEeq, iUnion_inter]
    exact iUnion_mono fun i => by rw [hLi i]; exact subset_closure
  obtain ⟨i₀, hi₀⟩ := irreducible_subset_finite_iUnion_closed hZ _
    (fun _ => isClosed_closure) hZsub
  obtain ⟨x, ⟨hxU, -⟩, hxZ⟩ := closure_nonempty_iff.mp (hZ.nonempty.mono hi₀)
  refine ⟨U i₀, C i₀, hU i₀, hC i₀, hi₀.trans (closure_minimal ?_ (hC i₀)), ⟨x, hxU, hxZ⟩, ?_⟩
  · exact fun _ ⟨⟨_, hxC⟩, _⟩ => hxC
  · rw [hEeq]
    exact fun y hy => mem_iUnion.mpr ⟨i₀, by rw [hLi i₀]; exact hy⟩

/-- **Stacks 005K**.
For irreducible `Z` and `E` a finite union of locally closed subsets, the intersection
`E ∩ Z` contains an open dense subset of `Z` if and only if it is dense in `Z`. -/
@[stacks 005K, ega "0 9.2.2", sga "1 IV 6.1" "necessity"]
theorem open_dense_iff_dense
    {Z : Set X} (hZ : IsIrreducible Z)
    {E : Set X} (hE : IsFiniteUnionLocallyClosed E) :
    (∃ V : Set X, IsOpenDenseSubsetOf V Z ∧ V ⊆ E ∩ Z) ↔ Z ⊆ closure (E ∩ Z) := by
  refine ⟨fun ⟨_, ⟨_, _, hVdense⟩, hVE⟩ => hVdense.trans (closure_mono hVE), fun h => ?_⟩
  obtain ⟨U, C, hU, -, hZC, hne, hUC⟩ := exists_open_closed_of_dense hZ hE h
  exact ⟨U ∩ Z, ⟨inter_subset_right, ⟨U, hU, rfl⟩,
    irreducible_subset_closure_open_inter hZ hU hne⟩, fun x ⟨hxU, hxZ⟩ => ⟨hUC ⟨hxU, hZC hxZ⟩, hxZ⟩⟩

/-- **Stacks 005K**.
For irreducible `Z` with generic point `ξ` and `E` a finite union of locally closed subsets,
the existence of an open dense subset of `Z` inside `E ∩ Z`, the density of `E ∩ Z` in `Z`,
and the membership `ξ ∈ E` are equivalent. -/
@[stacks 005K,
  ega "0 9.2.2" "Z has a generic point",
  ega "0 2.1.4" "partial",
  ega "0 9.2.5" "more general",
  ega "I 7.1.4" "partial",
  ega "IV 8.1.3" "partial", sga "1 IV 6.3" "special case", sga "1 IV 6.4" "(b)"]
theorem tfae_with_generic_point
    {Z : Set X} (hZ : IsIrreducible Z)
    {E : Set X} (hE : IsFiniteUnionLocallyClosed E)
    {ξ : X} (hξ : IsGenericPoint ξ Z) :
    [ (∃ V : Set X, IsOpenDenseSubsetOf V Z ∧ V ⊆ E ∩ Z),
      Z ⊆ closure (E ∩ Z),
      ξ ∈ E ].TFAE := by
  tfae_have 1 ↔ 2 := open_dense_iff_dense hZ hE
  tfae_have 2 → 3 := by
    intro h
    obtain ⟨U, C, hU, -, hZC, ⟨w, hwU, hwZ⟩, hUC⟩ := exists_open_closed_of_dense hZ hE h
    rw [← hξ] at hwZ
    obtain ⟨y, hyU, rfl⟩ := mem_closure_iff.mp hwZ U hU hwU
    exact hUC ⟨hyU, hZC hξ.mem⟩
  tfae_have 3 → 2 := fun hξE =>
    hξ.ge.trans (closure_mono (singleton_subset_iff.mpr ⟨hξE, hξ.mem⟩))
  tfae_finish

