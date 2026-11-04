module

public import StacksFrontier.RingTheory.FormsTrace.ChartExistence
public import StacksFrontier.RingTheory.FormsTrace.Existence

/-!
# Trace maps on forms of the universal charts

The universal chart rings `R = N_g[x_σ]` (for `g` syntomic-good and `σ` arbitrary) and the
comparison chart rings `R''[x_σ]` carry trace maps `Θ^p : Ω^p_{B_R} → Ω^p_R` with property (1)
of Stacks, Lemma 0FLB, linear over the forms of `R` and commuting with the de Rham differential.
For finitely many variables the ring is Noetherian and this is
`Stacks.FormsTrace.exists_isFormsTrace_of_isNoetherianRing` (the locally Noetherian case of the
proof of Lemma 0FLB, from Lemma 0FLA and the Tate isomorphism); in general the trace maps of the
finitely generated stages glue (`Stacks.FormsTrace.exists_isFormsTrace_universalChart_of_finite`).

## Main results

* `Stacks.FormsTrace.exists_isFormsTrace_universalChart`.
* `Stacks.FormsTrace.exists_isFormsTrace_comparisonChart`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra

universe u

namespace Stacks.FormsTrace

variable {d : ℕ} [NeZero d]

/-- **Trace maps on the forms of the universal charts.** -/
theorem exists_isFormsTrace_universalChart (σ : Type u) {g : universalRing d}
    (hg : IsSyntomicGood.{u} d g) :
    ∃ Θ : ∀ p : ℕ, ⋀[Carrier (tableOfHom (universalChartClassify σ g))]^p
        Ω[Carrier (tableOfHom (universalChartClassify σ g))⁄ℤ] →ₗ[universalChartRing σ g]
          ⋀[universalChartRing σ g]^p Ω[universalChartRing σ g⁄ℤ],
      IsFormsTrace (universalChartRing σ g) (Carrier (tableOfHom (universalChartClassify σ g))) Θ ∧
      IsWedgeLinear (universalChartRing σ g) (Carrier (tableOfHom (universalChartClassify σ g)))
        Θ ∧
      CommutesWithD (universalChartRing σ g) (Carrier (tableOfHom (universalChartClassify σ g)))
        Θ :=
  exists_isFormsTrace_universalChart_of_finite σ hg fun τ _ => by
    have := universalChartRing_isNoetherianRing τ hg
    have := universalChartRing_syntomic τ hg
    exact exists_isFormsTrace_of_isNoetherianRing _ _

/-- **Trace maps on the forms of the comparison charts.** -/
theorem exists_isFormsTrace_comparisonChart (σ : Type u) {g : universalRing d}
    (g' : universalRing d) (hg : IsSyntomicGood.{u} d g) :
    ∃ Θ : ∀ p : ℕ, ⋀[Carrier (tableOfHom (comparisonChartClassify g g' σ))]^p
        Ω[Carrier (tableOfHom (comparisonChartClassify g g' σ))⁄ℤ] →ₗ[comparisonChartRing g g' σ]
          ⋀[comparisonChartRing g g' σ]^p Ω[comparisonChartRing g g' σ⁄ℤ],
      IsFormsTrace (comparisonChartRing g g' σ)
        (Carrier (tableOfHom (comparisonChartClassify g g' σ))) Θ ∧
      IsWedgeLinear (comparisonChartRing g g' σ)
        (Carrier (tableOfHom (comparisonChartClassify g g' σ))) Θ ∧
      CommutesWithD (comparisonChartRing g g' σ)
        (Carrier (tableOfHom (comparisonChartClassify g g' σ))) Θ :=
  exists_isFormsTrace_comparisonChart_of_finite σ g' hg fun τ _ => by
    have := comparisonChartRing_isNoetherianRing (g' := g') (σ := τ) hg
    have := comparisonChartRing_syntomic (g' := g') (σ := τ) hg
    exact exists_isFormsTrace_of_isNoetherianRing _ _

end Stacks.FormsTrace

end
