module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 009I — Presheaves of sets on a basis

Stacks 009I defines presheaves of sets on a basis `B` for the topology of a space `X`.

Clause (1) is `PresheafOnBasis`: the data of a set `F(U)` for every `U ∈ B` together with
restriction maps `F(U) → F(V)` for every inclusion `V ⊆ U` of basis elements, subject to the
laws that restriction along the identity is the identity and that restriction is compatible
with composition of inclusions.

Clause (2) is `PresheafOnBasis.Hom`: a morphism `F → G` of presheaves on `B`, given by a map
`F(U) → G(U)` for each `U ∈ B` commuting with the restriction maps.

Both structures are defined here, indexed directly by membership in `B` rather than as
functors on a subcategory of the opens of `X`.
-/

@[expose] public section

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- A presheaf of sets on a basis `B` for the topology on `X`. -/
@[stacks 009I "(1) presheaf of sets on `B`: `F(U)` for `U ∈ B`, maps `ρ^U_V` for `V ⊆ U` \
  in `B`, `ρ^U_U = id`, `ρ^U_W = ρ^V_W ∘ ρ^U_V`; stated for any family `B` of subsets of `X`, \
  a basis of the topology in particular", ega "0 3.2.1" "set-valued definition"]
structure PresheafOnBasis (B : Set (Set X)) where
  /-- The set assigned to each basis open. -/
  obj : ∀ U ∈ B, Type*
  /-- The restriction map for each inclusion of basis opens. -/
  res : ∀ {U V : Set X} (hU : U ∈ B) (hV : V ∈ B), V ⊆ U → obj U hU → obj V hV
  /-- Restriction along the identity is the identity. -/
  res_self : ∀ {U : Set X} (hU : U ∈ B) (x : obj U hU),
    res hU hU (subset_refl U) x = x
  /-- Restriction is compatible with composition of inclusions. -/
  res_comp : ∀ {U V W : Set X} (hU : U ∈ B) (hV : V ∈ B) (hW : W ∈ B)
    (hWV : W ⊆ V) (hVU : V ⊆ U) (x : obj U hU),
    res hU hW (hWV.trans hVU) x = res hV hW hWV (res hU hV hVU x)

/-- A morphism of presheaves of sets on a basis `B`. -/
@[stacks 009I "(2) morphism `φ : F → G`: a map `F(U) → G(U)` for each `U ∈ B` compatible \
  with the restriction maps", ega "0 3.2.3" "morphism definition"]
structure PresheafOnBasis.Hom {B : Set (Set X)} (F G : PresheafOnBasis B) where
  /-- The component map at each basis open. -/
  app : ∀ {U : Set X} (hU : U ∈ B), F.obj U hU → G.obj U hU
  /-- Compatibility with restriction maps. -/
  naturality : ∀ {U V : Set X} (hU : U ∈ B) (hV : V ∈ B) (hVU : V ⊆ U)
    (x : F.obj U hU),
    app hV (F.res hU hV hVU x) = G.res hU hV hVU (app hU x)

