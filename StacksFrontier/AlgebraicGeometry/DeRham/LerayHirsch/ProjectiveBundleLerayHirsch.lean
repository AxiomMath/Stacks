module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LerayHirschTheorem
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleFibreBasis
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleRankZero
import StacksCore.Tactic.StacksAttribute

/-!
# The Leray--Hirsch isomorphism of a projective bundle

Let `g : X ⟶ S` be a morphism of schemes, `ℰ` an `𝒪_X`-module locally free of constant rank `r`
and `p : P = 𝐏(ℰ) ⟶ X` its projective bundle. This file proves the two isomorphism assertions of
Remark 0FUN of the Stacks project:

* the morphism `ξ̃ : ⨁_{0 ≤ t < r} Ω^•_{X/S}[-2t] ⟶ Rp_*Ω^•_{P/S}` of Proposition 0FMR for the
  classes `c₁^{dR}(𝒪_P(1))^t` is an isomorphism in `D(X, (X ⟶ S)^{-1}𝒪_S)`;
* for `r ≥ 1`, with `M = ⨁_{1 ≤ t < r} Ω^•_{X/S}[-2t]`, the morphism
  `c_{P/X} ⊕ ξ̃|_M : Ω^•_{X/S} ⊕ M ⟶ Rp_*Ω^•_{P/S}` is an isomorphism.

The first is Proposition 0FMR applied to `p`: `p` is smooth and proper (Section 0FMG) and the
restrictions of the classes `c₁^{dR}(𝒪_P(1))^t` to a fibre `P_y = ℙ^{r-1}_{κ(y)}` form a basis
of its de Rham cohomology (Lemma 0FMJ). For `r = 0` the bundle is empty, so `p` is smooth and
proper and the fibre hypothesis holds with the empty basis. The second follows formally from the
first (`isIso_biprodDesc_of_isIso_lerayHirschPowerMorphism`).

For `r = 0` and `X` nonempty the second assertion fails (its target is zero and its source
contains `Ω^•_{X/S}`), and the "arrow for `t = 0`" the remark refers to exists only for `r ≥ 1`;
it is stated for `r ≥ 1`.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.isIso_projectiveBundleLerayHirschMorphism`
* `AlgebraicGeometry.DeRhamLerayHirsch.isIso_biprodDesc_projectiveBundleLerayHirschMorphism`

## References

* [Stacks Project, Tag 0FUN](https://stacks.math.columbia.edu/tag/0FUN)
* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DeRhamDirectImage
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase)
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X S : Scheme.{u}} (g : X ⟶ S) (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]

/-- **Stacks Project, Remark 0FUN: the Leray--Hirsch morphism of a projective bundle is an
isomorphism.** For `ℰ` locally free of constant rank `r` and `p : P = 𝐏(ℰ) ⟶ X`, the morphism
`ξ̃ = ⨁_t ξ̃_t[-2t] : ⨁_{0 ≤ t < r} Ω^•_{X/S}[-2t] ⟶ Rp_*Ω^•_{P/S}` attached to the classes
`c₁^{dR}(𝒪_P(1))^t ∈ H^{2t}_{dR}(P/S)` is an isomorphism in `D(X, (X ⟶ S)^{-1}𝒪_S)`. -/
@[stacks 0FUN "in the situation of Proposition 0FMT (E locally free of constant rank r on X, \
X -> S, p : P = P(E) -> X), the map xi~ : (+)_{t = 0, ..., r-1} Omega_{X/S}[-2t] -> \
Rp_*Omega_{P/S} attached to the classes c_1^dR(O_P(1))^t is an isomorphism in \
D(X, (X -> S)^{-1}O_S)"]
theorem isIso_projectiveBundleLerayHirschMorphism :
    IsIso (projectiveBundleLerayHirschMorphism g E r) := by
  rcases r with _ | n
  · have := Stacks.ProjectiveBundleDeRham.isEmpty_projectiveBundle_of_rank_zero E
    have : Smooth (projectiveBundleToBase X E) := inferInstance
    have : IsProper (projectiveBundleToBase X E) := inferInstance
    refine isIso_lerayHirschMorphism _ g _ _ fun y => ?_
    have : IsEmpty ((projectiveBundleToBase X E).fiber y) :=
      Function.isEmpty ((projectiveBundleToBase X E).fiberι y).base
    have : ∀ m : ℤ, Subsingleton ↥(fibreDeRhamModule (projectiveBundleToBase X E) y m) :=
      fun m => Stacks.ProjectiveBundleDeRham.subsingleton_deRhamCohomology_of_isEmpty
        ((projectiveBundleToBase X E).fiberToSpecResidueField y) m
    exact ⟨Module.Basis.empty _, fun i => i.elim0⟩
  · have := Stacks.ProjectiveBundleFibre.smooth_projectiveBundleToBase E n
    have := Stacks.ProjectiveBundleFibre.isProper_projectiveBundleToBase_of_rank E n
    exact isIso_lerayHirschMorphism _ g _ _
      (Stacks.ProjectiveBundleDeRham.exists_basis_fibreClassOverS_classPow g E n)

/-- **Stacks Project, Remark 0FUN: `c_{P/X} ⊕ ξ̃|_M` is an isomorphism.** For `ℰ` locally free of
constant rank `r ≥ 1` and `M = ⨁_{1 ≤ t < r} Ω^•_{X/S}[-2t]`, the morphism
`c_{P/X} ⊕ ξ̃|_M : Ω^•_{X/S} ⊕ M ⟶ Rp_*Ω^•_{P/S}` is an isomorphism. -/
@[stacks 0FUN "with M = (+)_{t = 1, ..., r-1} Omega_{X/S}[-2t], the map c_{P/X} (+) xi~|_M : \
Omega_{X/S} (+) M -> Rp_*Omega_{P/S} is an isomorphism; stated for r >= 1, the remark's arrow \
for t = 0 presupposing it (for r = 0 and X nonempty the target is 0 and the source is not)"]
theorem isIso_biprodDesc_projectiveBundleLerayHirschMorphism (hr : 0 < r) :
    IsIso (biprod.desc (deRhamDirectImageMap (projectiveBundleToBase X E) g)
      (powerSummandsTailι g 2 r ≫ projectiveBundleLerayHirschMorphism g E r)) :=
  have := isIso_projectiveBundleLerayHirschMorphism g E r
  isIso_biprodDesc_of_isIso_lerayHirschPowerMorphism _ g 2 (projectiveBundleChernClass g E) r hr

end AlgebraicGeometry.DeRhamLerayHirsch

end
