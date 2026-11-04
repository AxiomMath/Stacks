module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClasses

/-!
# Additivity of Chern classes along an invertible subsheaf, from the Segre operations

In Situation 0EDT let `X/B` be good and let `0 → ℒ → ℰ → ℱ → 0` be a short exact sequence of
finite locally free `𝒪_X`-modules of ranks `1`, `r`, `r - 1`. Write `t_i(ℰ)`, `t_i(ℱ)` for the
Segre operations and `x = c₁(ℒ)`. The geometry of the projective bundles gives

* `t_0(ℰ) = 1` (Stacks 0ERU),
* `x` commutes with every `t_i(ℰ)`,
* `t_{n+1}(ℰ) = t_{n+1}(ℱ) + x t_n(ℰ)` for every `n`,

the last because `𝐏(ℱ) ⊆ 𝐏(ℰ)` is the zero scheme of the section of `𝒪(1) ⊗ π^*ℒ^{∨}` induced by
`ℒ ⟶ ℰ`. This file deduces from these the identity `c(ℰ) = c(ℒ) c(ℱ)` of Stacks 0ES8 degree by
degree: `c_{n+1}(ℰ) = c_{n+1}(ℱ) + x c_n(ℱ)`. It is the formal computation of
`AlgebraicGeometry.Space.PrivateChern.chernSeq_succ_eq_of_segre`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCap_succ_eq_of_segreCap`: the deduction.

## References

* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **The Chern classes along an invertible subsheaf, from the three properties of the Segre
operations.** If `x` commutes with the Segre operations of `ℰ`, `t_0(ℰ) = 1` and
`t_{n+1}(ℰ) = t_{n+1}(ℱ) + x t_n(ℰ)` for all `n`, then `c_{n+1}(ℰ) = c_{n+1}(ℱ) + x c_n(ℱ)` for
all `n`. -/
theorem chernCap_succ_eq_of_segreCap (E F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (r s : ℕ) (hE : IsFiniteLocallyFreeOfRank D sX hX E r)
    (hF : IsFiniteLocallyFreeOfRank D sX hX F s) (x : AddMonoid.End (chowHomology.{u, v} D sX hX))
    (h0 : segreCapOfModule.{u, v} E r hE 0 = 1)
    (hx : ∀ i, Commute x (segreCapOfModule.{u, v} E r hE i))
    (h : ∀ n, segreCapOfModule.{u, v} E r hE (n + 1) =
      segreCapOfModule.{u, v} F s hF (n + 1) + x * segreCapOfModule.{u, v} E r hE n) (n : ℕ) :
    chernCap.{u, v} E r hE (n + 1) =
      chernCap.{u, v} F s hF (n + 1) + x * chernCap.{u, v} F s hF n :=
  chernSeq_succ_eq_of_segre _ _ x h0 hx h n

/-- **The Whitney deduction with the class applied first.** If `t₀(ℰ) = 1` and
`t_{n+1}(ℰ) = t_{n+1}(ℱ) + t_n(ℰ) ∘ x` for every `n` — `x` acting first, which is the form the
geometry of `𝐏(ℱ) ⊂ 𝐏(ℰ)` produces — then `c_{n+1}(ℰ) = c_{n+1}(ℱ) + x ∘ c_n(ℱ)`; no
commutativity of `x` with the Segre operations is needed. -/
theorem chernCap_succ_eq_of_segreCap_mul (E F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (r s : ℕ) (hE : IsFiniteLocallyFreeOfRank D sX hX E r)
    (hF : IsFiniteLocallyFreeOfRank D sX hX F s) (x : AddMonoid.End (chowHomology.{u, v} D sX hX))
    (h0 : segreCapOfModule.{u, v} E r hE 0 = 1)
    (h : ∀ n, segreCapOfModule.{u, v} E r hE (n + 1) =
      segreCapOfModule.{u, v} F s hF (n + 1) + segreCapOfModule.{u, v} E r hE n * x) (n : ℕ) :
    chernCap.{u, v} E r hE (n + 1) =
      chernCap.{u, v} F s hF (n + 1) + x * chernCap.{u, v} F s hF n :=
  chernSeq_succ_eq_of_segre_mul _ _ x h0 h n

end AlgebraicGeometry.Space.PrivateChern

end
