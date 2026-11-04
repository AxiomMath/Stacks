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
public import Mathlib.Topology.Maps.Proper.UniversallyClosed
public import Mathlib.Topology.Sheaves.Init

/-!
# Quasi-compactness via closed projections

A topological space `X` is quasi-compact exactly when the projection `Z × X → Z` is a closed
map for every topological space `Z`. This is the Bourbaki characterization of
quasi-compactness, and no separation hypothesis is imposed on any of the spaces involved.

## Main results

* `compactSpace_iff_forall_isClosedMap_fst`: quasi-compactness of `X` is equivalent to closedness
  of the projection
  `Prod.fst : Z × X → Z` for every `Z`.
* `compactSpace_iff_isClosed_image_fst`: the same criterion phrased in terms of images of closed
  subsets of
  `Z × X` under `Prod.fst`.
-/

@[expose] public section

universe u

/-- If the projection `Prod.fst : Z × X → Z` is a closed map for every `Z : Type u`, then `X`
is quasi-compact. -/
private lemma compactSpace_of_isClosedMap_fst (X : Type u) [TopologicalSpace X]
    (h : ∀ (Z : Type u) [TopologicalSpace Z], IsClosedMap (Prod.fst : Z × X → Z)) :
    CompactSpace X := by
  -- We show the constant map `X → PUnit` is universally closed, hence proper, hence
  -- `X` is compact (via `isProperMap_const_iff` over the T1 space `PUnit`).
  rw [← isProperMap_const_iff (PUnit.unit.{u + 1} : PUnit.{u + 1})]
  rw [isProperMap_iff_universally_closed]
  refine ⟨continuous_const, fun Z _ => ?_⟩
  -- The map `Prod.map (fun _ : X => PUnit.unit) id : X × Z → PUnit × Z` factors as
  --   (X × Z) --prodComm--> (Z × X) --Prod.fst--> Z --(punitProd Z).symm--> PUnit × Z.
  -- Each homeo is a closed map, and `Prod.fst : Z × X → Z` is closed by hypothesis.
  have heq :
      (Prod.map (fun _ : X => PUnit.unit.{u + 1}) (id : Z → Z)) =
        (Homeomorph.punitProd.{u} Z).symm ∘
          (Prod.fst : Z × X → Z) ∘
          (Homeomorph.prodComm X Z) := by
    funext p
    rfl
  rw [heq]
  exact ((Homeomorph.punitProd.{u} Z).symm.isClosedMap).comp
    ((h Z).comp (Homeomorph.prodComm X Z).isClosedMap)

/-- **Stacks 005P**.
A topological space `X` is quasi-compact (`CompactSpace X`) if and only if, for every
topological space `Z`, the first projection `Prod.fst : Z × X → Z` is a closed map. -/
@[stacks 005P]
theorem compactSpace_iff_forall_isClosedMap_fst (X : Type u) [TopologicalSpace X] :
    CompactSpace X ↔
      ∀ (Z : Type u) [TopologicalSpace Z], IsClosedMap (Prod.fst : Z × X → Z) := by
  refine ⟨fun _ Z _ => ?_, compactSpace_of_isClosedMap_fst X⟩
  exact isClosedMap_fst_of_compactSpace

/-- A topological space `X` is quasi-compact if and only if for every topological space `Z`
and every closed subset `M ⊆ Z × X`, the image `Prod.fst '' M ⊆ Z` is closed. -/
theorem compactSpace_iff_isClosed_image_fst (X : Type u) [TopologicalSpace X] :
    CompactSpace X ↔
      ∀ (Z : Type u) [TopologicalSpace Z] (M : Set (Z × X)),
        IsClosed M → IsClosed (Prod.fst '' M) :=
  compactSpace_iff_forall_isClosedMap_fst X

