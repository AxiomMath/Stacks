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
public import Mathlib.SetTheory.ZFC.PSet
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
# Locally closed quasi-compact subsets are constructible

In a quasi-compact space with a basis of quasi-compact opens closed under pairwise
intersections, every locally closed quasi-compact subset whose complement is retrocompact
is constructible.

## Main definitions

* `IsConstructibleStratified`: a finite union `⋃ p ∈ s, p.1 ∩ p.2ᶜ`, indexed by a `Finset`
  of pairs of retrocompact open subsets.

## Main results

* `IsRetrocompact.open_inter`: the intersection of a retrocompact open set with a
  retrocompact set is retrocompact.
* `exists_finite_basis_cover_subset`: a quasi-compact subset of an open set is covered by
  finitely many basis elements contained in that open set.
* `basis_isRetrocompact`: basis elements are retrocompact when the basis is closed under
  pairwise quasi-compact intersection.
* `main_theorem0F2K`: a locally closed quasi-compact subset with retrocompact complement is
  constructible.
-/

@[expose] public section


variable {X : Type*} [TopologicalSpace X]

/-- A subset `E ⊆ X` is *constructible* if it can be written as a finite union
of subsets of the form `U ∩ Vᶜ` where `U` and `V` are open and retrocompact
in `X`. We encode the finite union via a `Finset` of pairs `(U, V)`. -/
@[ega "IV 10.1.1", ega "IV 8.3.9", sga "3 VIB 3.7"]
def IsConstructibleStratified (E : Set X) : Prop :=
  ∃ s : Finset (Set X × Set X),
    (∀ p ∈ s, IsOpen p.1 ∧ IsRetrocompact p.1 ∧
              IsOpen p.2 ∧ IsRetrocompact p.2) ∧
    E = ⋃ p ∈ s, p.1 ∩ p.2ᶜ

/-- If `U` is open and retrocompact, and `E` is retrocompact, then `U ∩ E` is
retrocompact. -/
lemma IsRetrocompact.open_inter
    {U : Set X} (hUopen : IsOpen U) (hUretro : IsRetrocompact U)
    {E : Set X} (hEretro : IsRetrocompact E) :
    IsRetrocompact (U ∩ E) := by
  intro K hKcomp hKopen
  rw [show (U ∩ E) ∩ K = E ∩ (U ∩ K) by ext; grind]
  exact hEretro (hUretro hKcomp hKopen) (hUopen.inter hKopen)

/-- A compact subset of an open set is covered by finitely many basis elements,
all contained in that open set. -/
lemma exists_finite_basis_cover_subset
    (B : Set (Set X)) (hB : TopologicalSpace.IsTopologicalBasis B)
    {T U : Set X} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ s : Set (Set X), s ⊆ B ∧ s.Finite ∧ T ⊆ ⋃₀ s ∧ ∀ W ∈ s, W ⊆ U := by
  choose! f hfB hfx hfU using
    fun (x : X) (hx : x ∈ T) => hB.exists_subset_of_mem_open (hTU hx) hU
  obtain ⟨F, hF_sub, hF_fin, hF_cover⟩ :=
    hT.elim_finite_subcover_image (b := T) (c := f)
      (fun x hx => hB.isOpen (hfB x hx))
      (fun x hx => Set.mem_biUnion hx (hfx x hx))
  refine ⟨f '' F, ?_, hF_fin.image f, ?_, ?_⟩
  · rintro W ⟨x, hxF, rfl⟩
    exact hfB x (hF_sub hxF)
  · intro x hx
    obtain ⟨W, hWmem, hxW⟩ := Set.mem_iUnion₂.mp (hF_cover hx)
    exact ⟨f W, ⟨W, hWmem, rfl⟩, hxW⟩
  · rintro W ⟨x, hxF, rfl⟩
    exact hfU x (hF_sub hxF)

/-- Basis elements are retrocompact when the basis is closed under pairwise
compact intersection. -/
@[ega "IV 1.8.1" "more general"]
lemma basis_isRetrocompact
    (B : Set (Set X)) (hB : TopologicalSpace.IsTopologicalBasis B)
    (hBinter : ∀ U ∈ B, ∀ V ∈ B, IsCompact (U ∩ V))
    {W : Set X} (hW : W ∈ B) : IsRetrocompact W := by
  intro K hKcompact hKopen
  obtain ⟨s, hs_subB, hs_fin, hs_cover, hs_subK⟩ :=
    exists_finite_basis_cover_subset B hB hKcompact hKopen (subset_refl K)
  have hKeq : K = ⋃₀ s := subset_antisymm hs_cover (Set.sUnion_subset hs_subK)
  rw [show W ∩ K = ⋃₀ ((W ∩ ·) '' s) by
    rw [hKeq]; ext; simp [Set.mem_inter_iff, Set.mem_sUnion]]
  refine (hs_fin.image _).isCompact_sUnion ?_
  rintro T ⟨V, hVs, rfl⟩
  exact hBinter W hW V (hs_subB hVs)

/-- **Stacks 0F2K**.
In a quasi-compact space having a basis of quasi-compact opens closed under pairwise
intersections, a locally closed subset `T ⊆ X` that is quasi-compact and whose complement
`Tᶜ` is retrocompact in `X` is constructible in `X`. -/
@[stacks 0F2K, ega "0 9.1.5" "special case", ega "IV 1.8.1" "partial"]
theorem main_theorem0F2K
    [CompactSpace X]
    (B : Set (Set X))
    (hB : TopologicalSpace.IsTopologicalBasis B)
    (_hBcompact : ∀ U ∈ B, IsCompact U)
    (hBinter : ∀ U ∈ B, ∀ V ∈ B, IsCompact (U ∩ V))
    (T : Set X)
    (hTlc : IsLocallyClosed T)
    (hTqc : IsCompact T)
    (hTcRetro : IsRetrocompact Tᶜ) :
    IsConstructibleStratified T := by
  -- Locally closed presentation T = U ∩ Z.
  obtain ⟨U, Z, hUopen, hZclosed, hTUZ⟩ := hTlc
  -- Cover T by finitely many basis elements inside U; let U₀ be their union.
  obtain ⟨s, hsB, hsfin, hscover, hsU⟩ :=
    exists_finite_basis_cover_subset B hB hTqc hUopen
      (fun x hx => (hTUZ ▸ hx).1)
  set U₀ : Set X := ⋃₀ s with hU₀def
  have hU₀open : IsOpen U₀ := isOpen_sUnion fun W hW => hB.isOpen (hsB hW)
  have hTeq_UZ : T = U₀ ∩ Z := by
    refine Set.Subset.antisymm (fun x hx => ⟨hscover hx, (hTUZ ▸ hx).2⟩) ?_
    rintro x ⟨⟨W, hWs, hxW⟩, hxZ⟩
    exact hTUZ ▸ ⟨hsU W hWs hxW, hxZ⟩
  -- `V := U₀ ∩ Tᶜ` equals `U₀ ∩ Zᶜ`, so it is open; it is also retrocompact.
  set V : Set X := U₀ ∩ Tᶜ with hVdef
  have hVopen : IsOpen V := by
    rw [show V = U₀ ∩ Zᶜ by rw [hVdef, hTeq_UZ]; ext; simp; tauto]
    exact hU₀open.inter hZclosed.isOpen_compl
  have hU₀retro : IsRetrocompact U₀ := by
    rw [show U₀ = ⋃ W ∈ s, W by simp [hU₀def, Set.sUnion_eq_biUnion]]
    exact .biUnion hsfin fun W hW => basis_isRetrocompact B hB hBinter (hsB hW)
  have hVretro : IsRetrocompact V :=
    IsRetrocompact.open_inter hU₀open hU₀retro hTcRetro
  -- `T = U₀ ∩ Vᶜ` via the singleton finset `{(U₀, V)}`.
  refine ⟨{(U₀, V)}, ?_, ?_⟩
  · simpa using ⟨hU₀open, hU₀retro, hVopen, hVretro⟩
  · simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, hVdef]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, not_and, not_not]
    exact ⟨fun hxT => ⟨hscover hxT, fun _ => hxT⟩, fun ⟨hxU₀, h⟩ => h hxU₀⟩

