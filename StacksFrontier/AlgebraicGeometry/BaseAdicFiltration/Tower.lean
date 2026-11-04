module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.GradedPiece
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroTower

/-!
# The adic filtration as the index of a tower of square-zero extensions

`Stacks.Thickenings.exists_thickening_of_iterate` realizes a sheaf of rings with nilpotent kernel
by applying [Stacks, Tag 05YV] once per step of a filtration whose successive quotients are
square-zero, and takes the number `N` of steps as a parameter.  This file supplies that `N` for
the `𝔪`-adic filtration over an Artinian local base, and records the inequality on ideal sheaves
which is the reason the successive quotients of an adic filtration are square-zero at all.

Together these say: the iteration of Tag 05YV that [Stacks, Tag 0E3X] performs is finite, and its
length is the order of nilpotence of `𝔪`.

## Main results

* `Stacks.BaseAdicFiltration.baseIdeal_pow_sq_le_pow_succ`: **why the steps are square-zero.**
  For `i ≥ 1` the square of the `i`-th step `Iⁱ𝒪_U` of the filtration lies in the `(i+1)`-st,
  because `i + 1 ≤ 2i`; so `Iⁱ𝒪_U/Iⁱ⁺¹𝒪_U` is a square-zero ideal of `𝒪_U/Iⁱ⁺¹𝒪_U`, which is
  the hypothesis `Stacks.Thickenings.SquareZeroExtension.square_zero` asks for at each step.
  This fails for `i = 0`: `𝒪_U/I𝒪_U` is not a square-zero extension of anything, which is why
  the tower starts at the special fibre rather than below it.
* `Stacks.BaseAdicFiltration.exists_thickening_of_isArtinianRing`: **the iteration terminates.**
  Over an Artinian local base the tower of square-zero extensions reaches the stage at which the
  `𝔪`-adic filtration of `ℱ` is zero, and at that stage one gets a single scheme over the base
  satisfying the invariant, with a thickening of the bottom stage into it.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.BaseAdicFiltration

variable {A : Type u} [CommRing A] {U : Scheme.{u}}

/-- **The successive quotients of an adic filtration are square-zero.** For `i ≥ 1` the square of
the `i`-th step `Iⁱ𝒪_U` of the filtration of the structure sheaf is contained in the `(i+1)`-st,
since `i + 1 ≤ 2i`; equivalently, the ideal `Iⁱ𝒪_U/Iⁱ⁺¹𝒪_U` of `𝒪_U/Iⁱ⁺¹𝒪_U` has square zero.

This is the inequality that makes the filtration of [Stacks, Tag 0E3X] usable as the index of a
tower of square-zero extensions: the kernel `𝔪·f_*𝒪_U` of `f_*𝒪_U ⟶ 𝒪_Y` is not square-zero, but
each of the `n` kernels obtained by filtering it is, and
`Stacks.Thickenings.exists_thickening_of_iterate` consumes them one at a time.

The hypothesis `1 ≤ i` cannot be dropped: for `i = 0` the statement would read `𝒪_U ≤ I𝒪_U`.

The same inequality for an ideal of a ring, rather than for an ideal sheaf, is
`AlgebraicGeometry.FormalSpace.adicStage_sq_le_succ`, which indexes the affine tower of
[Stacks, Tag 0AIF] and dodges the side condition by numbering its stages from `I ^ (n + 1)`;
the ideal-sheaf statement is obtained the same way, from
`AlgebraicGeometry.Scheme.IdealSheafData.pow_le_pow_of_le`. -/
theorem baseIdeal_pow_sq_le_pow_succ (p : U ⟶ Spec (CommRingCat.of A)) (I : Ideal A) {i : ℕ}
    (hi : 1 ≤ i) : (baseIdeal p I ^ i) ^ 2 ≤ baseIdeal p I ^ (i + 1) := by
  rw [← pow_mul]
  exact Scheme.IdealSheafData.pow_le_pow_of_le _ (by omega)

/-- **Over an Artinian local base the tower of square-zero extensions is finite, of length the
order of nilpotence of `𝔪`.**

Let `P` be an invariant of schemes over `S` graded by `ℕ`, holding at level `0` of
`g₀ : Y₀ ⟶ S` and propagating across one application of [Stacks, Tag 05YV].  Then there is an
`N` at which the `𝔪`-adic filtration of `ℱ` is already zero, and a single scheme `V` over `S`
satisfying `P` at level `N`, with a thickening `Y₀ ⟶ V` over `S`.

`Stacks.BaseAdicFiltration.exists_adicFiltration_eq_bot_of_isArtinianRing` supplies the `N`, and
that is the only place nilpotence of `𝔪` enters: the steps themselves need only
`Stacks.BaseAdicFiltration.baseIdeal_pow_sq_le_pow_succ`.  For [Stacks, Tag 0E3X] the invariant
is the identification of the structure sheaf of the stage `n` with `f_*(𝒪_U/𝔪ⁿ⁺¹𝒪_U)`, so that
at the top stage, where `𝔪^N ℱ = 0`, it reads `𝒪_V ≅ f_*𝒪_U` — the conclusion the tag's
essential surjectivity needs. -/
theorem exists_thickening_of_isArtinianRing [IsArtinianRing A] [IsLocalRing A]
    (p : U ⟶ Spec (CommRingCat.of A)) (F : U.Modules) {S : Scheme.{u}}
    (P : ℕ → (Y : Scheme.{u}) → (Y ⟶ S) → Prop) {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ S}
    (h₀ : P 0 Y₀ g₀)
    (hstep : ∀ (n : ℕ) (Y : Scheme.{u}) (g : Y ⟶ S), P n Y g →
      ∃ E : Stacks.Thickenings.SquareZeroExtension g,
        ∃ r : Stacks.Thickenings.Realization E, P (n + 1) r.ambient r.toBase) :
    ∃ (N : ℕ) (V : Scheme.{u}) (g : V ⟶ S) (i : Y₀ ⟶ V),
      adicFiltration p (IsLocalRing.maximalIdeal A) N F = ⊥ ∧ P N V g ∧
        Stacks.Thickenings.IsThickening i ∧ i ≫ g = g₀ := by
  obtain ⟨N, hN⟩ := exists_adicFiltration_eq_bot_of_isArtinianRing p F
  obtain ⟨V, g, i, hP, hi, hig⟩ :=
    Stacks.Thickenings.exists_thickening_of_iterate N P h₀ fun n Y g _ h => hstep n Y g h
  exact ⟨N, V, g, i, hN, hP, hi, hig⟩

end Stacks.BaseAdicFiltration

end
