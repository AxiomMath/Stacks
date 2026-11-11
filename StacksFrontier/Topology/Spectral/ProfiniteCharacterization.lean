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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Sheaves.Init

/-!
# Characterization of profinite spectral spaces

For a spectral space `X`, Stacks 0905 lists eight equivalent conditions: `X` is profinite
(quasi-compact, Hausdorff and totally disconnected), `X` is Hausdorff, `X` is totally
disconnected, every quasi-compact open of `X` is closed, there are no nontrivial specializations,
every point of `X` is closed, every point of `X` is the generic point of an irreducible component,
and the constructible topology of `X` equals its given topology. This file proves the
implications among the first seven conditions that need neither the constructible topology nor
Stacks 0903; the remaining implications and the full statement, `spectralSpace_profinite_tfae`,
are in `StacksFrontier.Topology.Spectral.ProfiniteCharacterizationTFAE`.

A Hausdorff spectral space is profinite: `T₂` makes every quasi-compact open closed, hence
clopen, and the quasi-compact opens form a topological basis, so `T₀` forces total separation.

## Main results

* `totallySeparatedSpace_of_qcOpen_isClosed`: a spectral space whose quasi-compact opens are
  closed is totally separated.
* `trivial_specialization_iff_t1Space`: triviality of specialization is the `T₁` axiom.
* `trivial_specialization_iff_isGenericPoint_irreducibleComponent`: on a spectral space,
  specialization is trivial exactly when every point is the generic point of an irreducible
  component.
* `spectralSpace_profinite_of_t2`: a Hausdorff spectral space is profinite.
* `profinite_iff_t2`: for a spectral space, being profinite is equivalent to being Hausdorff.
-/

@[expose] public section

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- In a Hausdorff space every quasi-compact open subset is closed: this is just
`IsCompact.isClosed`. -/
theorem isClosed_qcOpen_of_t2 [T2Space X]
    (U : Set X) (hKc : IsCompact U) : IsClosed U :=
  hKc.isClosed

/-- A spectral space in which every quasi-compact open is closed (equivalently,
clopen, since it is already open) is totally separated.

The proof uses the fact that the quasi-compact opens form a topological basis on
a (pre)spectral space; combined with `T₀` (automatic from `SpectralSpace`) and
the hypothesis that quasi-compact opens are closed, the space has a clopen
basis, and `T₀` then forces total separation. -/
theorem totallySeparatedSpace_of_qcOpen_isClosed [SpectralSpace X]
    (h : ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U) :
    TotallySeparatedSpace X := by
  refine ⟨?_⟩
  intro x _ y _ hxy
  -- Quasi-compact opens form a topological basis on a prespectral space.
  have hBasis : TopologicalSpace.IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U} :=
    PrespectralSpace.isTopologicalBasis
  -- Use T₀ to separate `x` and `y` by a basis element.
  have hnIns : ¬ Inseparable x y := fun h => hxy (T0Space.t0 h)
  rw [hBasis.inseparable_iff] at hnIns
  push Not at hnIns
  obtain ⟨U, ⟨hUopen, hUcomp⟩, hxy'⟩ := hnIns
  have hU : IsClopen U := ⟨h U hUopen hUcomp, hUopen⟩
  rcases hxy' with ⟨hxU, hyU⟩ | ⟨hxU, hyU⟩
  · exact ⟨U, Uᶜ, hU.isOpen, hU.compl.isOpen, hxU, hyU, fun z _ => em (z ∈ U),
      disjoint_compl_right⟩
  · exact ⟨Uᶜ, U, hU.compl.isOpen, hU.isOpen, hxU, hyU, fun z _ => (em (z ∈ U)).symm,
      disjoint_compl_left⟩

/-- A spectral space in which every quasi-compact open is closed is totally
disconnected. -/
theorem totallyDisconnectedSpace_of_qcOpen_isClosed [SpectralSpace X]
    (h : ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U) :
    TotallyDisconnectedSpace X :=
  have : TotallySeparatedSpace X := totallySeparatedSpace_of_qcOpen_isClosed h
  TotallySeparatedSpace.totallyDisconnectedSpace X

/-- A spectral space in which every quasi-compact open is closed is Hausdorff,
since it is totally separated. -/
theorem t2Space_of_qcOpen_isClosed [SpectralSpace X]
    (h : ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U) :
    T2Space X :=
  have : TotallySeparatedSpace X := totallySeparatedSpace_of_qcOpen_isClosed h
  inferInstance

/-- In a totally disconnected space, there are no nontrivial specializations:
`x ⤳ y` forces `x = y`. The proof uses that `closure {x}` is connected and
contains `x`, hence equals `{x}` by total disconnectedness, and `x ⤳ y` puts
`y` in this singleton. -/
theorem eq_of_specializes_of_totallyDisconnected
    [TotallyDisconnectedSpace X] {x y : X} (hxy : x ⤳ y) : x = y := by
  -- `connectedComponent x = {x}` by total disconnectedness.
  have hcc : connectedComponent x = ({x} : Set X) :=
    totallyDisconnectedSpace_iff_connectedComponent_singleton.1 inferInstance x
  -- `closure {x} ⊆ connectedComponent x` because the closure of a connected set
  -- is connected, contains `x`, and the connected component is the maximal
  -- connected set containing `x`.
  have hcl_sub_cc : closure ({x} : Set X) ⊆ connectedComponent x :=
    isPreconnected_singleton.closure.subset_connectedComponent (subset_closure rfl)
  -- `x ⤳ y` ↔ `y ∈ closure {x}`.
  have hy_mem_cl : y ∈ closure ({x} : Set X) := specializes_iff_mem_closure.mp hxy
  have hy_mem_cc : y ∈ connectedComponent x := hcl_sub_cc hy_mem_cl
  have : y ∈ ({x} : Set X) := hcc ▸ hy_mem_cc
  simpa [eq_comm] using this

/-- A totally disconnected space has only trivial specializations. -/
theorem trivial_specialization_of_totallyDisconnected
    [TotallyDisconnectedSpace X] :
    ∀ x y : X, x ⤳ y → x = y :=
  fun _ _ hxy => eq_of_specializes_of_totallyDisconnected hxy

/-- Triviality of specialization is exactly the `T₁` axiom: `T₁` is equivalent
to `∀ x y, x ⤳ y → x = y`. This is `t1Space_iff_specializes_imp_eq` from
Mathlib. -/
theorem trivial_specialization_iff_t1Space :
    (∀ x y : X, x ⤳ y → x = y) ↔ T1Space X :=
  t1Space_iff_specializes_imp_eq.symm

/-- Forward direction of (5) ⇔ (7) for spectral spaces.

If `X` is spectral and has no nontrivial specializations, then every point of
`X` is the generic point of some irreducible component. -/
theorem isGenericPoint_irreducibleComponent_of_trivial_specialization
    [SpectralSpace X] (h : ∀ x y : X, x ⤳ y → x = y) :
    ∀ x : X, ∃ Z ∈ irreducibleComponents X, IsGenericPoint x Z := by
  intro x
  -- Pick an irreducible component containing `x`.
  have hx_irr : IsIrreducible (closure ({x} : Set X)) :=
    isIrreducible_singleton.closure
  obtain ⟨Z, hZ, hsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ hx_irr
  have hxZ : x ∈ Z := hsub (subset_closure rfl)
  -- Quasi-sobriety gives a generic point `η` of `Z`.
  have hIrrZ : IsIrreducible Z := hZ.1
  have hClosedZ : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η Z := QuasiSober.sober hIrrZ hClosedZ
  -- `η ⤳ x`, and the hypothesis forces `η = x`.
  have hspec : η ⤳ x := by
    rw [specializes_iff_mem_closure, hη]; exact hxZ
  have heq : η = x := h η x hspec
  refine ⟨Z, hZ, ?_⟩
  rw [IsGenericPoint, ← heq]
  exact hη

/-- Backward direction of (5) ⇔ (7) for spectral spaces.

If every point of a spectral space is the generic point of an irreducible
component, then specialization is trivial. -/
theorem trivial_specialization_of_isGenericPoint_irreducibleComponent
    [SpectralSpace X]
    (h : ∀ x : X, ∃ Z ∈ irreducibleComponents X, IsGenericPoint x Z) :
    ∀ x y : X, x ⤳ y → x = y := by
  intro x y hxy
  obtain ⟨Zy, hZy_mem, hZy_gen⟩ := h y
  obtain ⟨Zx, hZx_mem, hZx_gen⟩ := h x
  have hclos : closure ({y} : Set X) ⊆ closure ({x} : Set X) :=
    Specializes.closure_subset hxy
  rw [hZy_gen, hZx_gen] at hclos
  -- Maximality of the irreducible component `Zy`.
  have hZx_irr : IsIrreducible Zx := hZx_mem.1
  have hrev : Zx ⊆ Zy := hZy_mem.2 hZx_irr hclos
  have hZy_eq : Zy = Zx := le_antisymm hclos hrev
  have hxgen' : IsGenericPoint x Zy := hZy_eq ▸ hZx_gen
  exact hxgen'.eq hZy_gen

/-- For a spectral space, triviality of specialization is equivalent to every point being the
generic point of an irreducible component. -/
theorem trivial_specialization_iff_isGenericPoint_irreducibleComponent
    [SpectralSpace X] :
    (∀ x y : X, x ⤳ y → x = y) ↔
      (∀ x : X, ∃ Z ∈ irreducibleComponents X, IsGenericPoint x Z) :=
  ⟨isGenericPoint_irreducibleComponent_of_trivial_specialization,
   trivial_specialization_of_isGenericPoint_irreducibleComponent⟩

/-- A Hausdorff spectral space is totally disconnected.

Since a spectral space is quasi-compact, `T2` implies that every quasi-compact open is closed
(`IsCompact.isClosed`), hence clopen. The quasi-compact opens form a topological basis on a
spectral space, so the space has a clopen basis, which together with `T₀` yields total separation
and hence total disconnectedness. -/
theorem totallyDisconnectedSpace_of_t2 [SpectralSpace X] [T2Space X] :
    TotallyDisconnectedSpace X :=
  totallyDisconnectedSpace_of_qcOpen_isClosed (fun _ _ hKc => hKc.isClosed)

/-- A Hausdorff spectral space is profinite: it is both Hausdorff and totally disconnected
(quasi-compactness is automatic from `SpectralSpace`). This is the implication (2) ⇒ (1) of
Stacks 0905; the full list of equivalences is `spectralSpace_profinite_tfae`. -/
theorem spectralSpace_profinite_of_t2 [SpectralSpace X] [T2Space X] :
    T2Space X ∧ TotallyDisconnectedSpace X :=
  ⟨inferInstance, totallyDisconnectedSpace_of_t2⟩

/-- For a spectral space `X`, the conjunction "`X` is Hausdorff and totally
disconnected" is equivalent to "`X` is Hausdorff": the second is automatic
in the first direction, while the converse is the substantive part of
Stacks 0905. -/
theorem profinite_iff_t2 [SpectralSpace X] :
    (T2Space X ∧ TotallyDisconnectedSpace X) ↔ T2Space X :=
  ⟨And.left, fun h => ⟨h, @totallyDisconnectedSpace_of_t2 X _ _ h⟩⟩
