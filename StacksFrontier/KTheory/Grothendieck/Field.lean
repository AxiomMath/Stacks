module
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Algebra.Order.Star.Int
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
@[expose] public section


open CategoryTheory

universe u

/-- Over a field `k`, the (finite) dimension function is additive on short
exact sequences of `k`-vector spaces in `ModuleCat.{u} k`: if
`0 → X₁ → X₂ → X₃ → 0` is short exact and `X₂` is finite-dimensional, then
`finrank k X₂ = finrank k X₁ + finrank k X₃`.

This is the core computation underlying the informal Stacks remark that
`K₀(k) = K'₀(k) ≅ ℤ` for a field `k`, with the isomorphism given by the
dimension/length function. Indeed, this additivity is exactly the condition
that makes `finrank` descend to a well-defined homomorphism from the
Grothendieck group of finitely generated `k`-modules to `ℤ`. -/
@[stacks 00JE, sga "6 I 6.0" "(ii), special case"]
theorem finrank_additive_of_shortExact {k : Type u} [Field k]
    (S : ShortComplex (ModuleCat.{u} k))
    (hfin : Module.Finite k S.X₂)
    (hS : S.ShortExact) :
    Module.finrank k S.X₂ = Module.finrank k S.X₁ + Module.finrank k S.X₃ := by
  have hf_inj : Function.Injective S.f.hom := hS.moduleCat_injective_f
  have hg_surj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  have hker_eq : LinearMap.range S.f.hom = LinearMap.ker S.g.hom :=
    hS.exact.moduleCat_range_eq_ker
  have h_rn : Module.finrank k (LinearMap.range S.g.hom)
      + Module.finrank k (LinearMap.ker S.g.hom) = Module.finrank k S.X₂ :=
    LinearMap.finrank_range_add_finrank_ker (S.g.hom)
  have h_range_g : Module.finrank k (LinearMap.range S.g.hom) =
      Module.finrank k S.X₃ := by
    rw [LinearMap.range_eq_top.mpr hg_surj, finrank_top]
  have h_ker : Module.finrank k (LinearMap.ker S.g.hom) =
      Module.finrank k (LinearMap.range S.f.hom) := by
    rw [hker_eq]
  have h_range_f : Module.finrank k (LinearMap.range S.f.hom) =
      Module.finrank k S.X₁ :=
    LinearMap.finrank_range_of_inj hf_inj
  linarith [h_rn, h_range_g, h_ker, h_range_f]

