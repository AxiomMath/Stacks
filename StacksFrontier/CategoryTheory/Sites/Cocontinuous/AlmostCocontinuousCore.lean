module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
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
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs

/-!
# A morphism with the universal property of the sheafification

If a sheaf `E` and a presheaf morphism `η₀ : F ⟶ E` satisfy the universal property of the
sheafification of `F`, then the transpose `F^# ⟶ E` of `η₀` under the sheafification adjunction
is an isomorphism. This is the general fact that two solutions of one universal problem are
isomorphic, and holds on any site.

Stacks 04B8 itself, `(u^p G)^# = u^p(G^#)` for a continuous, almost cocontinuous functor of sites
`u` and a presheaf `G` with a single section over every sheaf theoretically empty object, is
`CategoryTheory.Functor.isIso_homEquiv_symm_whiskerLeft_toSheafify_of_isAlmostCocontinuous` in
`StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousFunctors`.
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]

/-- **A solution of the universal problem of sheafification is the sheafification.** Suppose a
sheaf `E` together with a presheaf morphism `η₀ : F ⟶ (sheafToPresheaf J _).obj E` satisfies the
universal property of the sheafification of `F`: every presheaf morphism from `F` into the
underlying presheaf of any sheaf `H` lifts uniquely through `η₀`. Then the canonical morphism
`(presheafToSheaf J).obj F ⟶ E` obtained from `η₀` via the sheafification adjunction's `homEquiv`
is an isomorphism.

This is a general fact about adjunctions, on a single site. It is not Stacks 04B8, which is
`CategoryTheory.Functor.isIso_homEquiv_symm_whiskerLeft_toSheafify_of_isAlmostCocontinuous`. -/
theorem isIso_sheafificationAdjunction_homEquiv_symm
    (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type v)]
    (F : Cᵒᵖ ⥤ Type v)
    (E : Sheaf J (Type v))
    (η₀ : F ⟶ (sheafToPresheaf J (Type v)).obj E)
    (h_exists : ∀ (H : Sheaf J (Type v))
                  (α : F ⟶ (sheafToPresheaf J (Type v)).obj H),
        ∃ β : E ⟶ H, η₀ ≫ (sheafToPresheaf J (Type v)).map β = α)
    (h_unique : ∀ (H : Sheaf J (Type v)) (β₁ β₂ : E ⟶ H),
        η₀ ≫ (sheafToPresheaf J (Type v)).map β₁ =
          η₀ ≫ (sheafToPresheaf J (Type v)).map β₂ → β₁ = β₂) :
    IsIso (((sheafificationAdjunction J (Type v)).homEquiv _ _).symm η₀) := by
  -- Abbreviations for the adjunction, its unit, and the morphism.
  set adj := sheafificationAdjunction J (Type v)
  set φ : (presheafToSheaf J (Type v)).obj F ⟶ E := (adj.homEquiv F E).symm η₀
    with hφ_def
  -- Defining identity for `φ`: `unit ≫ map φ = η₀` via `homEquiv_unit`.
  have hφ_eq :
      adj.unit.app F ≫ (sheafToPresheaf J (Type v)).map φ = η₀ := by
    have h := adj.homEquiv_unit (X := F) (Y := E) (f := φ)
    -- `h : adj.homEquiv F E φ = unit ≫ map φ`.
    have happly : adj.homEquiv F E φ = η₀ := Equiv.apply_symm_apply _ η₀
    exact h.symm.trans happly
  -- Candidate inverse `ψ : E ⟶ (presheafToSheaf).obj F`.
  obtain ⟨ψ, hψ⟩ :=
    h_exists ((presheafToSheaf J (Type v)).obj F) (adj.unit.app F)
  -- `ψ ≫ φ = 𝟙 E` by `h_unique`.
  have h_psi_phi : ψ ≫ φ = 𝟙 E := by
    apply h_unique
    have lhs : η₀ ≫ (sheafToPresheaf J (Type v)).map (ψ ≫ φ) = η₀ := by
      rw [Functor.map_comp, ← Category.assoc, hψ]
      exact hφ_eq
    have rhs : η₀ ≫ (sheafToPresheaf J (Type v)).map (𝟙 E) = η₀ := by simp
    exact lhs.trans rhs.symm
  -- `φ ≫ ψ = 𝟙` by injectivity of the adjunction's `homEquiv`: both sides
  -- map to `adj.unit.app F` under `homEquiv`.
  have h_phi_psi : φ ≫ ψ = 𝟙 ((presheafToSheaf J (Type v)).obj F) := by
    apply (adj.homEquiv F ((presheafToSheaf J (Type v)).obj F)).injective
    -- Compute `homEquiv (φ ≫ ψ)`.
    have hLHS :
        adj.homEquiv F ((presheafToSheaf J (Type v)).obj F) (φ ≫ ψ)
          = adj.unit.app F := by
      rw [adj.homEquiv_unit, (sheafToPresheaf J (Type v)).map_comp]
      -- Goal (after left-associating implicitly): unit ≫ map φ ≫ map ψ = unit.
      -- Use `reassoc` of `hφ_eq` and then `hψ`.
      have hφ_reassoc :
          (adj.unit.app F ≫ (sheafToPresheaf J (Type v)).map φ) ≫
              (sheafToPresheaf J (Type v)).map ψ
            = η₀ ≫ (sheafToPresheaf J (Type v)).map ψ :=
        congrArg (· ≫ (sheafToPresheaf J (Type v)).map ψ) hφ_eq
      simp only [Category.assoc] at hφ_reassoc
      exact hφ_reassoc.trans hψ
    -- Compute `homEquiv 𝟙`.
    have hRHS :
        adj.homEquiv F ((presheafToSheaf J (Type v)).obj F)
          (𝟙 ((presheafToSheaf J (Type v)).obj F))
          = adj.unit.app F := by
      rw [adj.homEquiv_unit]; simp
    exact hLHS.trans hRHS.symm
  exact ⟨ψ, h_phi_psi, h_psi_phi⟩

