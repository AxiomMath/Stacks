module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveEmbedding
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafRank
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections of an ideal twist of large degree

In Situation [Stacks, Tag 0B5D] let `X` be integral of genus `g`, let `ℒ` be invertible and let
`Z ⊆ X` be a zero-dimensional closed subscheme with ideal `ℐ`. If
`deg(ℒ) > 2g - 2 + deg(Z)` then `H¹(X, ℐℒ) = 0`, and either `H⁰(X, ℐℒ) ≠ 0`, or `g = 0` and
`deg(ℒ) = deg(Z) - 1`. This is [Stacks, Tag 0E3B].

The vanishing is the contrapositive of the degree bound of [Stacks, Tag 0E3A]. If moreover
`H⁰(X, ℐℒ) = 0` then `χ(X, ℐℒ) = 0`, while Riemann–Roch gives
`χ(X, ℐℒ) = deg(ℒ) + 1 - g - deg(Z)`; the degree hypothesis then forces `g = 0`.

## Main results

* `AlgebraicGeometry.CohenMacaulayCurveSituation.isZero_cohomology_one_idealTwist_of_lt` —
  `H¹(X, ℐℒ) = 0`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.not_isZero_cohomology_zero_idealTwist_or_of_lt` —
  `H⁰(X, ℐℒ) ≠ 0`, or `g = 0` and `deg(ℒ) = deg(Z) - 1`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.exists_isIso_projectiveLine_of_genus_eq_zero` —
  in case (2) with `Z = ∅`, that is `g = 0` and `deg(ℒ) = -1`: `X ≅ 𝐏¹_k` over `k` with `ℒ^{⊗ -1}`
  the pullback of `𝒪(1)` ([Stacks, Tag 0C6T]).

## Implementation notes

`Z = ∅` has `deg(Z) = 0`, so case (2) with `Z = ∅` is the hypothesis `g = 0 ∧ deg(ℒ) = -1`, which
is how the last clause is stated. `𝐏¹_k` is `AlgebraicGeometry.projectiveSpaceOver 1 (Spec k)` and
`𝒪(1)` is pulled back from the integral model, the spelling of [Stacks, Tag 01NE] in this library;
"`ℒ` corresponds to `𝒪(-1)`" is stated as `ℒ^{⊗ -1} ≅ p^*𝒪(1)`.

## References

* [Stacks Project, Tag 0E3B](https://stacks.math.columbia.edu/tag/0E3B)
* [Stacks Project, Tag 0E3A](https://stacks.math.columbia.edu/tag/0E3A)
* [Stacks Project, Tag 0C6T](https://stacks.math.columbia.edu/tag/0C6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u}) [IsIntegral S.X] (L : S.X.Modules)
  [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
  (Z : S.X.IdealSheafData)

/-- **[Stacks, Tag 0E3B], the vanishing.** If `deg(ℒ) > 2g - 2 + deg(Z)` then
`H¹(X, ℐℒ) = 0`: a nonzero `H¹(X, ℐℒ)` would force `deg(ℒ) ≤ 2g - 2 + deg(Z)` by
[Stacks, Tag 0E3A]. -/
@[stacks 0E3B "the vanishing of H^1(X, IL)"]
theorem isZero_cohomology_one_idealTwist_of_lt (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (hdeg : 2 * (genus S.f : ℤ) - 2 + (S.subschemeDegree Z : ℤ) <
      invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) :
    IsZero (cohomologyOverField S.k S.f (S.idealTwist Z L) 1) := by
  by_contra h
  exact (S.invertibleCurveDegree_le_of_not_isZero_cohomology_idealTwist L Z hZ h).not_gt hdeg

/-- **[Stacks, Tag 0E3B], the alternative.** If `deg(ℒ) > 2g - 2 + deg(Z)` then either
`H⁰(X, ℐℒ) ≠ 0`, or `g = 0` and `deg(ℒ) = deg(Z) - 1`. When `H⁰(X, ℐℒ) = 0` the Euler
characteristic `χ(X, ℐℒ) = deg(ℒ) + 1 - g - deg(Z)` vanishes, `H¹(X, ℐℒ)` vanishing as well. -/
@[stacks 0E3B "possibilities (1) and (2)"]
theorem not_isZero_cohomology_zero_idealTwist_or_of_lt (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (hdeg : 2 * (genus S.f : ℤ) - 2 + (S.subschemeDegree Z : ℤ) <
      invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) :
    ¬ IsZero (cohomologyOverField S.k S.f (S.idealTwist Z L) 0) ∨
      (genus S.f = 0 ∧ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L =
        (S.subschemeDegree Z : ℤ) - 1) := by
  by_cases h0 : IsZero (cohomologyOverField S.k S.f (S.idealTwist Z L) 0)
  · right
    have := S.isCoherent_idealTwist Z L
    have hχ := S.eulerCharacteristic_idealTwist Z hZ L
    unfold eulerCharacteristic at hχ
    rw [finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero S.k S.f _
      (isZero_cohomologyOverField_two_le S.k S.f (le_of_eq S.dimension_one) _)] at hχ
    have e0 : Module.finrank S.k (cohomologyOverField S.k S.f (S.idealTwist Z L) 0) = 0 := by
      have := ModuleCat.subsingleton_of_isZero h0
      exact Module.finrank_zero_of_subsingleton
    have e1 : Module.finrank S.k (cohomologyOverField S.k S.f (S.idealTwist Z L) 1) = 0 := by
      have := ModuleCat.subsingleton_of_isZero
        (S.isZero_cohomology_one_idealTwist_of_lt L Z hZ hdeg)
      exact Module.finrank_zero_of_subsingleton
    rw [e0, e1] at hχ
    exact ⟨by omega, by omega⟩
  · exact Or.inl h0

open Stacks.SheafOfModules.Invertible (tensorPowerModule) in
/-- **[Stacks, Tag 0E3B], case (2) with `Z = ∅`.** If `g = 0` and `deg(ℒ) = -1`, then `X ≅ 𝐏¹_k`
over `k`, and under this isomorphism `ℒ^{⊗ -1}` is the pullback of `𝒪(1)`, i.e. `ℒ` corresponds to
`𝒪_{𝐏¹}(-1)`. The invertible module `ℒ^{⊗ -1}` has degree one, so a basis of its two-dimensional
space of global sections defines an isomorphism `X ⟶ 𝐏¹_k` ([Stacks, Tag 0C6T]) along which
`𝒪(1)` pulls back to `ℒ^{⊗ -1}`. -/
@[stacks 0E3B "in case (2) with Z empty, X is P^1_k and L corresponds to O(-1)"]
theorem exists_isIso_projectiveLine_of_genus_eq_zero
    (hgenus : genus S.f = 0)
    (hdeg : invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L = -1) :
    ∃ p : S.X ⟶ projectiveSpaceOver 1 (Spec (.of S.k)),
      IsIso p ∧
      p ≫ Limits.pullback.fst (Limits.terminal.from (Spec (.of S.k)))
          (Limits.terminal.from (projectiveSpaceAtUniverse.{u} 1)) = S.f ∧
      Nonempty ((Scheme.Modules.pullback
          (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of S.k)))).obj
            (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 1) ≅
          tensorPowerModule L (-1)) := by
  have hM : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.property
      (tensorPowerModule L (-1)) :=
    Stacks.SheafOfModules.Invertible.tensorPower_isInvertible S.X.presheaf
      S.X.ringCatSheaf.property L (-1)
  have : Stacks.Ample.IsInvertibleModule S.X (tensorPowerModule L (-1)) := hM
  have hdegM :
      invertibleCurveDegree S.k S.f S.dimension_one.le (tensorPowerModule L (-1)) = 1 := by
    have := invertibleCurveDegree_tensorPower S.k S.f S.dimension_one.le L (-1)
    rw [hdeg] at this
    exact this.trans (by norm_num)
  set M := tensorPowerModule L (-1)
  let V := (restrictScalarsOverBase S.k S.f).obj
    ((_root_.SheafOfModules.evaluation S.X.ringCatSheaf (Opposite.op (⊤ : S.X.Opens))).obj M)
  have hfin : Module.finrank S.k V = 2 := by
    have := finrank_globalSections_eq_invertibleCurveDegree_add_one S.k S.f S.dimension_one.le M
      hgenus (by rw [hdegM]; norm_num)
    rw [hdegM] at this
    exact_mod_cast this
  have : Module.Finite S.k V := Module.finite_of_finrank_eq_succ hfin
  let b : Module.Basis (Fin (1 + 1)) S.k V := Module.finBasisOfFinrankEq S.k V hfin
  obtain ⟨-, hs, -⟩ := isRelativelyVeryAmple_and_isClosedImmersion_of_basis S.f
    S.dimension_one.le hgenus M (d := 1) (by exact_mod_cast hdegM) one_pos b
  set σ : Fin (1 + 1) → Γ(M, ⊤) := fun j => (show Γ(M, ⊤) from b j)
  obtain ⟨α, hα, -⟩ := Stacks.TwistPullbackPinned.exists_iso_pullback_twistingSheafAtUniverse σ
    (Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse σ hs)
    (Stacks.ProjectiveFromSections.isOpenCover_nvCover_of_generatesStalks σ hs)
    (fun i => Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse σ hs i)
  refine ⟨Stacks.ProjectiveFromSections.toProjectiveSpaceOver σ hs S.f,
    isIso_toProjectiveSpaceOver_of_invertibleCurveDegree_eq_one S.f S.dimension_one hgenus M hdegM
      b hs,
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst σ hs S.f, ⟨?_⟩⟩
  rw [Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd]
  exact asIso α

end AlgebraicGeometry.CohenMacaulayCurveSituation
