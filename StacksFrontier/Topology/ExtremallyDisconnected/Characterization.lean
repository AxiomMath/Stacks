module

public import Mathlib.Topology.ExtremallyDisconnected
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
# Characterizations of extremally disconnected quasi-compact Hausdorff spaces

## Main definitions

* `HasContinuousSectionFromCompactT2`: every continuous surjection onto the space from a
  quasi-compact Hausdorff space admits a continuous section.
* `CompactT2.Projective`: every continuous map from the space to a quasi-compact
  Hausdorff space lifts along any continuous surjection of quasi-compact Hausdorff spaces.

## Main results

* `extremallyDisconnected_tfae` (Stacks 08YN): for a quasi-compact Hausdorff space these two
  properties are
  equivalent to extremal disconnectedness.
-/

@[expose] public section

universe u

/-- A topological space `X` has continuous sections from quasi-compact Hausdorff spaces if every
continuous surjection `f : Y → X` with `Y` quasi-compact Hausdorff admits a continuous `s` with
`f ∘ s = id`. -/
def HasContinuousSectionFromCompactT2 (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (f : Y → X), Continuous f → Function.Surjective f →
    ∃ s : X → Y, Continuous s ∧ f ∘ s = id

/-- For a quasi-compact Hausdorff space `X` the following are equivalent: `X` is extremally
disconnected; every continuous surjection onto `X` from a quasi-compact Hausdorff space has a
continuous section; `X` is projective among quasi-compact Hausdorff spaces, which is Mathlib's
`CompactT2.Projective`. -/
@[stacks 08YN]
theorem extremallyDisconnected_tfae (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    List.TFAE
      [ ExtremallyDisconnected X,
        HasContinuousSectionFromCompactT2 X,
        CompactT2.Projective X ] := by
  tfae_have h12 : 1 → 2 := fun hED _ _ _ _ f hf hfsurj =>
    CompactT2.projective_iff_extremallyDisconnected.mpr hED continuous_id hf hfsurj
  tfae_have h23 : 2 → 3 := by
    intro hSec Y Z _ _ _ _ _ _ g f hg hf hfsurj
    -- The pullback `P = {(x, y) | g x = f y}` is compact Hausdorff and projects
    -- continuously and surjectively onto `X`.
    let P : Set (X × Y) := {p | g p.1 = f p.2}
    have : CompactSpace P := isCompact_iff_compactSpace.mp
      (isClosed_eq (hg.comp continuous_fst) (hf.comp continuous_snd)).isCompact
    obtain ⟨s, hscont, hsec⟩ := hSec (fun p : P => p.val.fst)
      (continuous_fst.comp continuous_subtype_val)
      (fun x => (hfsurj (g x)).elim fun y hy => ⟨⟨(x, y), hy.symm⟩, rfl⟩)
    refine ⟨fun x => (s x).val.snd,
      continuous_snd.comp (continuous_subtype_val.comp hscont), funext fun x => ?_⟩
    have hP : g (s x).val.fst = f (s x).val.snd := (s x).property
    have hπs : (s x).val.fst = x := congrFun hsec x
    grind
  tfae_have h31 : 3 → 1 := fun hLift =>
    CompactT2.projective_iff_extremallyDisconnected.mp hLift
  tfae_finish
