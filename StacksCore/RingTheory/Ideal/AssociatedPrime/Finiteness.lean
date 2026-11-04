module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import StacksCore.LinearAlgebra.Span.Basic

/-!
# Filtrations of finite modules by cyclic quotients

The main result of this file is `Module.Finite.exists_relSeries_isQuotientEquivQuotientCyclic`
(Stacks 00KZ): every finite module `M` over a ring `R` admits a finite filtration
`0 = M₀ ≤ M₁ ≤ ⋯ ≤ Mₙ = M` whose successive quotients `Mᵢ₊₁ ⧸ Mᵢ` are cyclic, i.e. each isomorphic
to `R ⧸ Iᵢ` for some ideal `Iᵢ`.

The filtration is packaged as a `RelSeries` of the relation
`Submodule.IsQuotientEquivQuotientCyclic`, so the cyclicity of each successive quotient is recorded
in the relation itself and is recovered from `RelSeries.step`. This is the cyclic-quotient analogue
of `Submodule.IsQuotientEquivQuotientPrime` and
`IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime` (Stacks 00L0), and is proved for an
arbitrary ring `R` using the closed-form filtration `Submodule.filtrationOfFinGeneratingFamily`.

Since the quotients are only cyclic, not simple, this is *not* a composition series in general:
the covering relation `⋖` would force simple quotients, which requires `M` to have finite length.
-/

@[expose] public section

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- `N₁.IsQuotientEquivQuotientCyclic N₂` asserts that `N₁ ≤ N₂` and that the subquotient `N₂ ⧸ N₁`
is cyclic, i.e. isomorphic to `R ⧸ I` for some ideal `I` of `R`.

This is the cyclic-quotient analogue of `Submodule.IsQuotientEquivQuotientPrime`. -/
def IsQuotientEquivQuotientCyclic (N₁ N₂ : Submodule R M) : Prop :=
  N₁ ≤ N₂ ∧ ∃ I : Ideal R, Nonempty ((↥N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[R] R ⧸ I)

/-- Adjoining a single generator `a` to a submodule `N'` yields a cyclic subquotient:
`N'.IsQuotientEquivQuotientCyclic (N' ⊔ R ∙ a)`. -/
theorem isQuotientEquivQuotientCyclic_sup_span_singleton (N' : Submodule R M) (a : M) :
    N'.IsQuotientEquivQuotientCyclic (N' ⊔ Submodule.span R {a}) :=
  ⟨le_sup_left, exists_quotient_sup_span_singleton_equiv N' a⟩

variable (R) in
/-- Consecutive terms of `filtrationOfFinGeneratingFamily` have a cyclic quotient, since they differ
by a single generator (`filtrationOfFinGeneratingFamily_succ`). -/
theorem isQuotientEquivQuotientCyclic_filtrationOfFinGeneratingFamily {n : ℕ} (g : Fin n → M)
    (i : Fin n) : IsQuotientEquivQuotientCyclic (filtrationOfFinGeneratingFamily R g i.castSucc)
      (filtrationOfFinGeneratingFamily R g i.succ) := by
  rw [filtrationOfFinGeneratingFamily_succ]
  exact isQuotientEquivQuotientCyclic_sup_span_singleton _ (g i)

/-- Given a finite family `g : Fin n → M`, the submodule `span R (Set.range g)` admits a filtration
`0 ≤ ⋯ ≤ span R (Set.range g)`, packaged as a `RelSeries` of
`Submodule.IsQuotientEquivQuotientCyclic` (so the successive quotients are cyclic) whose terms are
all finitely generated. The filtration is `filtrationOfFinGeneratingFamily`, adding one generator at
a time. -/
theorem exists_relSeries_isQuotientEquivQuotientCyclic_of_family {n : ℕ} (g : Fin n → M) :
    ∃ X : RelSeries {(N₁, N₂) | N₁.IsQuotientEquivQuotientCyclic N₂},
      X.head = ⊥ ∧ X.last = Submodule.span R (Set.range g) ∧ ∀ i, Module.Finite R (X i) :=
  ⟨⟨n, filtrationOfFinGeneratingFamily R g,
      fun i => isQuotientEquivQuotientCyclic_filtrationOfFinGeneratingFamily R g i⟩,
    filtrationOfFinGeneratingFamily_zero R g, filtrationOfFinGeneratingFamily_last R g,
    fun i => filtrationOfFinGeneratingFamily_finite R g i⟩

end Submodule

/-- **Stacks 00KZ**.
Let `R` be a ring and `M` a finite `R`-module. Then `M` admits a finite filtration
`0 = M₀ ≤ M₁ ≤ ⋯ ≤ Mₙ = M`, packaged as a `RelSeries` of
`Submodule.IsQuotientEquivQuotientCyclic`, whose terms are finitely generated and whose successive
quotients `Mᵢ₊₁ ⧸ Mᵢ` are cyclic, i.e. each isomorphic to `R ⧸ Iᵢ` for some ideal `Iᵢ`.

The quotients are cyclic but not necessarily simple, so this is a filtration rather than a
composition series in the sense of `CompositionSeries` (which requires simple quotients, hence
finite length). -/
@[stacks 00KZ]
theorem Module.Finite.exists_relSeries_isQuotientEquivQuotientCyclic (R M : Type*) [Ring R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ X : RelSeries {(N₁, N₂) | N₁.IsQuotientEquivQuotientCyclic N₂},
      X.head = (⊥ : Submodule R M) ∧ X.last = ⊤ ∧ ∀ i, Module.Finite R (X i) := by
  obtain ⟨n, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (Module.Finite.fg_top (R := R) (M := M))
  obtain ⟨X, hhead, hlast, hfin⟩ :=
    Submodule.exists_relSeries_isQuotientEquivQuotientCyclic_of_family (R := R) g
  exact ⟨X, hhead, hlast.trans hg, hfin⟩
