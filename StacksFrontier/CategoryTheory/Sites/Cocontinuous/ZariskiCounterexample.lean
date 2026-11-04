module

public import Mathlib.Order.CompletePartialOrder
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

/-!
# A functor of small Zariski sites that is not cocontinuous

Stacks tag 00XV (Example 7.21.9).  For a topological space `X` and a subset `Z ⊆ X` with the
subspace topology, the functor `U ↦ Z ∩ U` from the opens of `X` to the opens of `Z` need not
be cocontinuous.  Take `X = ℝ` and `Z = ℝ ∖ {0}`, covered by `{z < 0}` together with the sets
`{z > 1/(n+1)}`.  No covering of `ℝ` has intersections with `Z` refining that covering: some
member of it contains `0`, hence contains both a negative point and positive points below any
prescribed bound, and no single member of the given covering of `Z` contains such a pair.
-/

@[expose] public section

open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X]

/-- The functor `u : X_Zar → Z_Zar`, `U ↦ Z ∩ U`, on objects (open sets). Concretely it
is the comap of `U` along the inclusion `↥Z → X`; as a set of the subspace `↥Z` it is
`{ z // (z : X) ∈ U }`, i.e. `Z ∩ U`. -/
noncomputable def uOpens (Z : Set X) (U : Opens X) : Opens (↥Z) :=
  U.comap ⟨(Subtype.val : ↥Z → X), continuous_subtype_val⟩

/-- Definition 2: `u : X_Zar → Z_Zar` is cocontinuous (with `u U = Z ∩ U`).
For every open `U` of `X` and every covering `{V j}` of `u U = Z ∩ U` in `Z_Zar`
(a family of opens of the subspace, indexed by an arbitrary type `J` in any universe,
whose union is `u U`), there is a covering `{W i}` of `U` in `X_Zar` (indexed by an
arbitrary type `I` in any universe) such that the family `{u(W i)}` refines `{V j}`:
for each `i` there is some `j` with `u(W i) ≤ V j`.

The index types `I` and `J` are allowed to live in arbitrary universes. -/
def CocontinuousZar (Z : Set X) : Prop :=
  ∀ (U : Opens X) {J : Type*} (V : J → Opens (↥Z)),
    (⨆ j, V j) = uOpens Z U →
    ∃ (I : Type*) (W : I → Opens X),
      (⨆ i, W i) = U ∧ ∀ i, ∃ j, uOpens Z (W i) ≤ V j

/-- Membership in `uOpens Z U` for a subspace point `z : ↥Z` is just membership of
the underlying point `(z : X)` in `U`. (Unfolds `comap`.) -/
theorem mem_uOpens {Z : Set X} {U : Opens X} {z : ↥Z} :
    z ∈ uOpens Z U ↔ (z : X) ∈ U :=
  Iff.rfl

-- The space and subset for the counterexample.
/-- The subset `Z₀ = ℝ \ {0}`, carrying the subspace topology. -/
abbrev Z₀ : Set ℝ := {x : ℝ | x ≠ 0}

/-- The witnessing covering of `Z₀ = ℝ \ {0}`, indexed by `Option ℕ`:
`V none = {z | (z:ℝ) < 0}` (the negative part) and
`V (some n) = {z | 1/(n+1) < (z:ℝ)}` (points exceeding `1/(n+1)`).
Each is open in the subspace `↥Z₀` (preimage of an open half-line under the
continuous coercion). -/
noncomputable def Vcover : Option ℕ → Opens (↥Z₀) := fun
  | none   => ⟨{z : ↥Z₀ | (z : ℝ) < 0}, isOpen_Iio.preimage continuous_subtype_val⟩
  | some n => ⟨{z : ↥Z₀ | (1 : ℝ)/(n+1) < (z : ℝ)}, isOpen_Ioi.preimage continuous_subtype_val⟩

/-- Step 2 of the informal proof: the family `Vcover` covers all of `↥Z₀`, i.e. its
supremum is `⊤ = uOpens Z₀ ⊤`. Every nonzero real is either negative (lands in
`V none`) or positive, and a positive `x` satisfies `1/(n+1) < x` for large `n`
(Archimedean). -/
theorem Vcover_iSup_eq_top : (⨆ j, Vcover j) = uOpens Z₀ ⊤ := by
  apply SetLike.ext
  intro z
  rw [mem_uOpens]
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  rw [TopologicalSpace.Opens.mem_iSup]
  rcases lt_or_gt_of_ne z.2 with hneg | hpos
  · exact ⟨none, hneg⟩
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    exact ⟨some n, hn⟩

/-- Key topological extraction (Step 4–5): if an open set `W : Opens ℝ` contains `0`,
then it contains a strictly negative point and a strictly positive point that is
below any prescribed positive bound `δ`. Concretely, for every `δ > 0` there are
reals `a < 0` and `0 < b` with `b < δ`, both lying in `W`. -/
theorem open_nhds_zero_has_neg_and_small_pos
    (W : Opens ℝ) (h0 : (0 : ℝ) ∈ W) :
    (∃ a : ℝ, a < 0 ∧ a ∈ W) ∧ ∀ δ : ℝ, 0 < δ → ∃ b : ℝ, 0 < b ∧ b < δ ∧ b ∈ W := by
  have hW : (W : Set ℝ) ∈ nhds (0 : ℝ) := W.isOpen.mem_nhds h0
  rw [Metric.mem_nhds_iff] at hW
  obtain ⟨ε, hε, hsub⟩ := hW
  have ball_mem : ∀ x : ℝ, |x| < ε → x ∈ W := by
    intro x hx
    have hxb : x ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact hx
    exact hsub hxb
  refine ⟨⟨-ε/2, ?_, ?_⟩, ?_⟩
  · linarith
  · apply ball_mem
    rw [abs_lt]
    constructor <;> linarith
  · intro δ hδ
    refine ⟨min (ε/2) (δ/2), ?_, ?_, ?_⟩
    · have h1 : 0 < ε / 2 := by linarith
      have h2 : 0 < δ / 2 := by linarith
      exact lt_min h1 h2
    · have : min (ε/2) (δ/2) ≤ δ/2 := min_le_right _ _
      linarith
    · apply ball_mem
      have hb : min (ε/2) (δ/2) ≤ ε/2 := min_le_left _ _
      have hbpos : 0 < min (ε/2) (δ/2) := lt_min (by linarith) (by linarith)
      rw [abs_lt]
      constructor <;> linarith

/-- ULift-indexed version of the covering, needed to apply a *hypothesis*
`h : CocontinuousZar.{0,u}` whose quantified index type `J` is forced to live in the
fixed (but arbitrary) universe `u` of the theorem. We index by `ULift.{u} (Option ℕ)`
and compose with `ULift.down`. -/
noncomputable def VcoverU.{u} : ULift.{u} (Option ℕ) → Opens (↥Z₀) :=
  fun j => Vcover j.down

/-- The ULifted covering still covers `↥Z₀`: its supremum is `uOpens Z₀ ⊤`. This is
just `Vcover_iSup_eq_top` transported across the bijection `ULift.{u} (Option ℕ) ≃
Option ℕ`. -/
theorem VcoverU_iSup_eq_top.{u} : (⨆ j, VcoverU.{u} j) = uOpens Z₀ ⊤ := by
  rw [← Vcover_iSup_eq_top]
  exact Equiv.ulift.iSup_comp (g := Vcover)

/-- Stacks Tag 00XV (Example 7.21.9): for `X = ℝ` and `Z = ℝ \ {0}` (with the subspace
topology), the functor `u : X_Zar → Z_Zar`, `U ↦ Z ∩ U`, is NOT cocontinuous. -/
@[stacks 00XV]
theorem real_punctured_uOpens_not_cocontinuous :
    ¬ CocontinuousZar (X := ℝ) {x : ℝ | x ≠ 0} := by
  -- Assume cocontinuity `h` and derive `False`.
  intro h
  -- Step 1–2: instantiate `h` at `U = ⊤` with the ULifted covering `VcoverU` of
  -- `uOpens Z₀ ⊤`. We must use `VcoverU` (index `ULift.{u} (Option ℕ)`) rather than
  -- the plain `Vcover`, because `h`'s quantified index type `J` is fixed at universe
  -- `u`; `Vcover` (indexed by `Option ℕ : Type 0`) would not typecheck as `V`.
  obtain ⟨I, W, hWsup, hWref⟩ := h ⊤ VcoverU VcoverU_iSup_eq_top
  -- Step 4: `⨆ i, W i = ⊤`, so `0 ∈ ⨆ i, W i`; extract `i₀` with `0 ∈ W i₀`.
  have h0mem : ∃ i₀, (0 : ℝ) ∈ W i₀ := by
    have h0top : (0 : ℝ) ∈ (⨆ i, W i) := by rw [hWsup]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at h0top
    exact h0top
  obtain ⟨i₀, hi₀⟩ := h0mem
  -- Refinement gives a single `j` with `uOpens Z₀ (W i₀) ≤ VcoverU j`, i.e.
  -- `≤ Vcover j.down`.
  obtain ⟨j, hj⟩ := hWref i₀
  -- Step 5: from `W i₀` open containing 0, get a negative point and a small positive point.
  obtain ⟨⟨a, ha_neg, ha_mem⟩, hpos⟩ := open_nhds_zero_has_neg_and_small_pos (W i₀) hi₀
  -- Now case on `j.down : Option ℕ` and derive a contradiction using `hj` (note
  -- `VcoverU j = Vcover j.down`) together with `mem_uOpens` and the definition of
  -- `Vcover`. Both points `a` and a chosen `b` are nonzero, hence give subspace points
  -- in `uOpens Z₀ (W i₀)`, which `hj` forces into `Vcover j.down`.
  have key : ∀ (x : ℝ) (hx : x ≠ 0), x ∈ W i₀ → (⟨x, hx⟩ : ↥Z₀) ∈ VcoverU j :=
    fun x hx hxW => hj (mem_uOpens.mpr hxW)
  obtain ⟨jd⟩ := j
  cases jd with
  | none =>
      -- A small positive point `b` would lie in `Vcover none = {z | z < 0}`: contradiction.
      obtain ⟨b, hb_pos, _, hb_mem⟩ := hpos 1 one_pos
      have hb : b < 0 := key b hb_pos.ne' hb_mem
      linarith
  | some n =>
      -- The negative point `a` would lie in `Vcover (some n) = {z | 1/(n+1) < z}`.
      have ha : (1 : ℝ) / (n + 1) < a := key a ha_neg.ne ha_mem
      have hpos' : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
