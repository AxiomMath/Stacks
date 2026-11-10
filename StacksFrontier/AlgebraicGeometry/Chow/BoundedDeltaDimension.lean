module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentKZeroDimensionFiltration
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
import StacksFrontier.KTheory.SerreQuotient

/-!
# Consequences of a bounded delta-dimension

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a scheme
locally of finite type over `S`. Section 42.58 of the Stacks Project assumes `δ_{X/S}` bounded,
and under it the Chow groups vanish outside the bound and the filtration by dimension of supports
of `K'₀(X)` is exhaustive.

If no point of `X` has relative dimension `k`, then `Z_k(X) = 0` and hence `CH_k(X) = 0`. If
every point of `X` has relative dimension at most `k`, then every coherent `𝒪_X`-module has
support of delta-dimension at most `k`, so `F_k K'₀(X) = K'₀(X)`.

## Main results

* `Stacks.Chow.cyclesOfDimension_eq_bot` — `Z_k(X) = 0` when no point of `X` has relative
  dimension `k`.
* `Stacks.Chow.chowGroup_eq_zero` — hence `CH_k(X) = 0`.
* `Stacks.Chow.coherentKZeroFiltration_eq_top` — the filtration by dimension of supports is
  exhaustive: `F_k K'₀(X) = K'₀(X)` as soon as every point of `X` has relative dimension at
  most `k`.

## References

* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 0FEV](https://stacks.math.columbia.edu/tag/0FEV)
* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- If no point of `X` has relative dimension `k` over the base, then `Z_k(X) = 0`. -/
theorem cyclesOfDimension_eq_bot {k : ℤ}
    (hk : ∀ x : X, relativeDimension C.dimensionFunction f x ≠ k) :
    cyclesOfDimension C f k = ⊥ := by
  refine le_antisymm (fun c hc => ?_) bot_le
  have h := (mem_cyclesOfDimension_iff_forall_point C f k c).1 hc
  rw [AddSubgroup.mem_bot]
  ext x
  by_contra hx
  exact hk x (h x (by simpa using hx))

/-- If no point of `X` has relative dimension `k` over the base, then `CH_k(X) = 0`. -/
theorem chowGroup_eq_zero {k : ℤ}
    (hk : ∀ x : X, relativeDimension C.dimensionFunction f x ≠ k)
    (α : chowGroup C f k) : α = 0 := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective α
  obtain rfl : c = 0 := Subtype.ext (by simpa [cyclesOfDimension_eq_bot C f hk] using c.2)
  simp

/-- The filtration of `K'₀(X)` by dimension of supports is exhaustive at any bound for the
relative dimension: if every point of `X` has relative dimension at most `hi` over the base,
then `F_{hi} K'₀(X) = K'₀(X)`. -/
theorem coherentKZeroFiltration_eq_top {hi : ℤ}
    (hhi : ∀ x : X, relativeDimension C.dimensionFunction f x ≤ hi) :
    coherentKZeroFiltration C f hi = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  intro x
  have hmem : ∀ G : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
      KZero.mk _ G ∈ (coherentKZeroFiltration C f hi).subtype.range := by
    intro G
    have hG : coherentModulesDimLE C f hi G := by
      have : _root_.SheafOfModules.IsCoherent G.obj :=
        AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent G.property
      exact schemeDeltaDimension_reducedSupport_le C f G.obj fun y _ => hhi y
    exact ⟨⟨_, mk_mem_coherentKZeroFiltration C f hi ⟨G, hG⟩⟩, rfl⟩
  obtain ⟨y, rfl⟩ := KZero.surjective_of_mk_mem_range _ hmem x
  exact y.2

end Stacks.Chow

end
