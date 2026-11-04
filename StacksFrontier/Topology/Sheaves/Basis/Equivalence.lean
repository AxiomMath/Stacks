module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves on a basis

Let `X` be a topological space, `B : ι → Opens X` a basis for the topology on `X`, and `C` a
category with enough limits. Restriction along the inclusion of `B` into `Opens X` is an
equivalence between sheaves on `X` valued in `C` and sheaves valued in `C` on `B` with the
topology induced from `Opens.grothendieckTopology X`.

## Main definitions

* `restrictBasisEquivalenceStructures`: the equivalence, for `B` whose inclusion is cover-dense.
* `restrictBasisEquivalenceStructures_of_isBasis`: the equivalence, for `B` a basis.
-/

@[expose] public section

universe w v u

open CategoryTheory TopologicalSpace Topology


/-- Let `X` be a topological space, let `B : ι → Opens X` be a family of opens whose inclusion
into `Opens X` is cover-dense, and let `C` be a category with enough limits. Then restriction
along the inclusion of `B` into `Opens X` is an equivalence from sheaves on `X` with values in
`C` to sheaves with values in `C` on the site `B` with the topology induced from
`Opens.grothendieckTopology X`. -/
@[stacks 009R, sga "4 III 4.1" "special case", sga "4 V 8.1.12" "special case"]
noncomputable def restrictBasisEquivalenceStructures
    {X : TopCat.{w}} {ι : Type w} (B : ι → Opens X)
    [(inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X)]
    (C : Type v) [Category.{u} C]
    [∀ Y, Limits.HasLimitsOfShape
        (CategoryTheory.StructuredArrow Y (inducedFunctor B).op) C] :
    Sheaf (Opens.grothendieckTopology X) C ≌
      Sheaf ((inducedFunctor B).inducedTopology
              (Opens.grothendieckTopology X)) C :=
  (Functor.sheafInducedTopologyEquivOfIsCoverDense
      (inducedFunctor B) (Opens.grothendieckTopology X) C).symm

/-- Restriction along the inclusion of a basis `B` of the topology on `X` is an equivalence from
sheaves on `X` with values in `C` to sheaves with values in `C` on the site `B` with the induced
topology. -/
@[sga "4 V 8.1.12" "special case"]
noncomputable def restrictBasisEquivalenceStructures_of_isBasis
    {X : TopCat.{w}} {ι : Type w} (B : ι → Opens X)
    (hB : Opens.IsBasis (Set.range B))
    (C : Type v) [Category.{u} C]
    [∀ Y, Limits.HasLimitsOfShape
        (CategoryTheory.StructuredArrow Y (inducedFunctor B).op) C] :
    letI : (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X) :=
      TopCat.Opens.coverDense_inducedFunctor hB
    Sheaf (Opens.grothendieckTopology X) C ≌
      Sheaf ((inducedFunctor B).inducedTopology
              (Opens.grothendieckTopology X)) C :=
  haveI : (inducedFunctor B).IsCoverDense (Opens.grothendieckTopology X) :=
    TopCat.Opens.coverDense_inducedFunctor hB
  restrictBasisEquivalenceStructures B C
