module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GlobalSectionsGeneration
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
public import Mathlib.LinearAlgebra.Dual.Lemmas
import StacksCore.Tactic.StacksAttribute

/-!
# Riemann-Roch for the dualizing sheaf of a proper curve

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `ω` be the dualizing sheaf of `X`. Section [Stacks, Tag 0B5B] relates the
Euler characteristics of `𝒪_X` and of `ω`, and the two consequences of that section which the
vanishing results for curves consume are proved here: the one-dimensionality of `H¹(X, ω)`, and
the count of global sections of the quotient in a presentation `0 ⟶ ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` whose
quotient has zero-dimensional support.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `CohenMacaulayCurveSituation.finrank_cohomologyOverField_one_eq_one_of_unitDual`:
  `dim_k H¹(X, ω) = 1`, which is the hypothesis `hone` of
  `AlgebraicGeometry.CohenMacaulayCurveSituation.nonempty_generatingSections_tensorSheaf`.
* `CohenMacaulayCurveSituation.eulerCharacteristic_unit_eq_neg_eulerCharacteristic_of_unitDual`:
  **Lemma 53.5.1 of Section [Stacks, Tag 0B5B]** in the Cohen--Macaulay case,
  `χ(X, 𝒪_X) = -χ(X, ω)`.
* `CohenMacaulayCurveSituation.finrank_cohomologyOverField_zero_eq_eulerCharacteristic_sub`:
  for a short exact sequence `0 ⟶ ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` of coherent modules whose quotient has
  zero-dimensional support, `dim_k H⁰(X, 𝒬) = χ(X, ℱ) - χ(X, ω)`.

## The duality, and where it is discharged

*The shape of the statements here.* Section [Stacks, Tag 0B5B] reads its relation between
`χ(X, 𝒪_X)` and `χ(X, ω)` off the duality

`Hⁱ(X, ω_X^•) = Ext^i(𝒪_X, ω_X^•) = Hom_k(H^{-i}(X, 𝒪_X), k)`,

which is clause (4) of [Stacks, Tag 0BS2] at `K = 𝒪_X`, read in the Cohen--Macaulay case
`ω_X^• = ω_X[1]` of [Stacks, Tag 0BS3]. The module `ω` is a free parameter of the results below,
so that duality is one of their inputs: it is the datum `e` at `i = 0`, and the pair `e₁` at
`i = 0` and `e₀` at `i = 1`, each a `k`-linear isomorphism of one cohomology group of `ω` with
the `k`-linear dual of one cohomology group of `𝒪_X`. That is the shape a consumer carrying a
dualizing sheaf of its own needs.

*At the canonical dualizing sheaf there is nothing to supply.* Clause (4) of
[Stacks, Tag 0BS2] is proved `k`-linearly as `Stacks.Duality.extDualityLinearEquiv`, and clause
(5) as `AlgebraicGeometry.CohenMacaulayCurveSituation`
`.firstCohomologyDuality_dualizingSheafOverField`. From those two,
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingEulerCharacteristic.lean` builds
both isomorphisms at `ω = Stacks.Duality.dualizingSheafOverField S.f` and proves
`χ(X, 𝒪_X) = -χ(X, ω_X)` there; that file is where Lemma 53.5.1 of Section [Stacks, Tag 0B5B]
and [Stacks, Tag 0BS5] are registered. The equality `dim_k H¹(X, ω_X) = 1` is proved outright,
for that same sheaf, in
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingFirstCohomologyDimension.lean`.

**`e₁` is not clause (5) of [Stacks, Tag 0BS2], and does not follow from it.** Clause (5),
which `AlgebraicGeometry.CohenMacaulayCurveSituation.FirstCohomologyDuality` carries, is
`Hom(ℱ, ω) = Hom_k(H¹(X, ℱ), k)`; at `ℱ = ω` it identifies `H¹(X, ω)^∨` with the ring `End(ω)`,
and `dim_k H¹(X, ω) = 1` is then the statement `End(ω) = k`, which is the part of the dualizing
property of `ω` that clause (5) does not express. Clause (5) together with Situation
[Stacks, Tag 0B5D] and the vanishing of `H²` admits the model `End(ω) = k[t]/(t²)`,
`H¹(X, ω) = End(ω)^∨`, with the trace functional a generator of the socle: the bijection and its
naturality hold, and `dim_k H¹(X, ω) = 2`. So `hone` is an input of the same kind as `hdual`,
not a consequence of it.

*What the results below prove.* Everything else. Situation [Stacks, Tag 0B5D] turns the duality
at `i = 0` into `dim_k H¹(X, ω) = 1`, because its `H⁰(X, 𝒪_X) = k` makes the dual of
`H⁰(X, 𝒪_X)`
one-dimensional; the two Euler characteristics collapse to `h⁰ - h¹` by [Stacks, Tag 02UZ] on
the one-dimensional `X`; and the count of global sections of `𝒬` is the additivity of the Euler
characteristic ([Stacks, Tag 08AA]) together with the vanishing of `H¹(X, 𝒬)` on a coherent
module with zero-dimensional support, which is the vanishing clause of [Stacks, Tag 0B3J].

*The count is the one Section [Stacks, Tag 0B5B] asks for, up to the rank of `ω`.* The
hypothesis `hsec` of
`AlgebraicGeometry.CohenMacaulayCurveSituation.nonempty_generatingSections_tensorSheaf` wants
`dim_k H⁰(X, 𝒬) = deg(ℒ)` for `ℱ = ω ⊗ ℒ`. By the result below that count is
`χ(X, ω ⊗ ℒ) - χ(X, ω)`, and [Stacks, Tag 0AYV] — which is proved with no hypothesis, as
`AlgebraicGeometry`
`.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_isCurve`
— evaluates that difference as `r·deg(ℒ)` with `r = dim_{κ(ξ)} ω_ξ` the rank of `ω` at the
generic point. So the count is `deg(ℒ)` exactly when `ω` has rank one, which is clause (2) of
[Stacks, Tag 0BS2]; at the canonical dualizing sheaf that clause rests on the dualizing-complex
property of `f^×(𝒪_{Spec k})`, which is clause (4)(a) of [Stacks, Section 0AU3]
(`Stacks.Duality.isDualizingComplex_upperShriek_obj`, read at `f^× = f^!` for the proper `f`);
that reading is not carried out here, so the rank is not used even there.

## Implementation notes

`AlgebraicGeometry.finrank_cohomologyOverField_unit_zero_eq_one` of
`StacksFrontier/AlgebraicGeometry/Curves/LinearSeries.lean` is used throughout.

The short exact sequence of the count is taken as a `CategoryTheory.ShortComplex` together with
`ShortComplex.ShortExact`, rather than as two maps and an exactness statement, so that the
coherence instances of [Stacks, Tag 08AA] are found at the spellings that lemma uses.

## References

* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 0BS5](https://stacks.math.columbia.edu/tag/0BS5)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0B3J](https://stacks.math.columbia.edu/tag/0B3J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable {S : CohenMacaulayCurveSituation.{u}}

/-- On the one-dimensional `X`, the Euler characteristic of a coherent module is `h⁰ - h¹`. -/
private theorem eulerCharacteristic_eq_sub_finrank (M : S.X.Modules) [M.IsCoherent] :
    eulerCharacteristic S.k S.f M =
      (Module.finrank S.k (cohomologyOverField S.k S.f M 0) : ℤ) -
        (Module.finrank S.k (cohomologyOverField S.k S.f M 1) : ℤ) :=
  eulerCharacteristic_eq_sub_of_isZero S.k S.f M fun m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le S.k S.f M (d := 1)
      (le_of_eq S.dimension_one) (by omega)

/-! ### One-dimensionality of the first cohomology of the dualizing sheaf -/

/-- **`dim_k H¹(X, ω) = 1`** in Situation [Stacks, Tag 0B5D], from the duality of `H¹(X, ω)`
with the `k`-linear dual of `H⁰(X, 𝒪_X)`.

This is the hypothesis `hone` of
`AlgebraicGeometry.CohenMacaulayCurveSituation.nonempty_generatingSections_tensorSheaf`. The
duality `e` is clause (4) of [Stacks, Tag 0BS2] at `K = 𝒪_X` and `i = 0`, read in the
Cohen--Macaulay case `ω_X^• = ω_X[1]` of [Stacks, Tag 0BS3]; it is an input because `ω` is a
free parameter here, and it is *not* a consequence of clause (5) of [Stacks, Tag 0BS2], as the
module documentation explains. What is proved here is that Situation [Stacks, Tag 0B5D] turns
it into the equality: its `H⁰(X, 𝒪_X) = k` makes the dual of `H⁰(X, 𝒪_X)` one-dimensional.

At `ω = Stacks.Duality.dualizingSheafOverField S.f` the datum `e` is
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.cohomologyOverFieldOneDualizingSheafLinearEquiv`, where the tags of this registration now
sit; the conclusion for that sheaf is proved outright as
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one`. -/
public theorem finrank_cohomologyOverField_one_eq_one_of_unitDual {ω : S.X.Modules}
    (e : cohomologyOverField S.k S.f ω 1 ≃ₗ[S.k]
      (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) 0 →ₗ[S.k] S.k)) :
    Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1 := by
  have hdual : Module.finrank S.k (Module.Dual S.k
      (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) 0)) = 1 := by
    rw [Subspace.dual_finrank_eq, finrank_cohomologyOverField_unit_zero_eq_one S.f]
  rw [e.finrank_eq]
  exact hdual

/-! ### Lemma 53.5.1 of Section 0B5B -/

/-- **Lemma 53.5.1 of Section [Stacks, Tag 0B5B]**, in the Cohen--Macaulay case:
`χ(X, 𝒪_X) = -χ(X, ω)`.

Both Euler characteristics collapse to `h⁰ - h¹` because `X` is one-dimensional, so
[Stacks, Tag 02UZ] kills cohomology above degree one. The duality gives
`dim_k H¹(X, ω) = dim_k H⁰(X, 𝒪_X) = 1` and `dim_k H⁰(X, ω) = dim_k H¹(X, 𝒪_X)`, so
`χ(X, ω) = dim_k H¹(X, 𝒪_X) - 1 = -χ(X, 𝒪_X)`.

The data `e₁` and `e₀` are inputs because `ω` is a free parameter here. At
`ω = Stacks.Duality.dualizingSheafOverField S.f` they are
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.cohomologyOverFieldOneDualizingSheafLinearEquiv` and
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.cohomologyOverFieldZeroDualizingSheafLinearEquiv`, and the conclusion with both Euler
characteristics written as the alternating sums that define them — which is what lets the
coherence of `ω_X` be dispensed with too — is
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.finsum_alternating_finrank_unit_eq_neg_dualizingSheaf`, where the tags sit for that sheaf. -/
public theorem eulerCharacteristic_unit_eq_neg_eulerCharacteristic_of_unitDual
    {ω : S.X.Modules} [ω.IsCoherent] [(SheafOfModules.unit S.X.ringCatSheaf).IsCoherent]
    (e₁ : cohomologyOverField S.k S.f ω 1 ≃ₗ[S.k]
      (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) 0 →ₗ[S.k] S.k))
    (e₀ : cohomologyOverField S.k S.f ω 0 ≃ₗ[S.k]
      (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) 1 →ₗ[S.k] S.k)) :
    eulerCharacteristic S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) =
      -eulerCharacteristic S.k S.f ω := by
  have h1 : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1 :=
    finrank_cohomologyOverField_one_eq_one_of_unitDual e₁
  have h0 : Module.finrank S.k (cohomologyOverField S.k S.f ω 0) =
      Module.finrank S.k
        (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) 1) := by
    rw [e₀.finrank_eq]
    exact Subspace.dual_finrank_eq
  have hu0 : Module.finrank S.k
      (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) 0) = 1 :=
    finrank_cohomologyOverField_unit_zero_eq_one S.f
  rw [eulerCharacteristic_eq_sub_finrank (SheafOfModules.unit S.X.ringCatSheaf),
    eulerCharacteristic_eq_sub_finrank ω, h1, h0, hu0]
  push_cast
  ring

/-! ### The count of global sections of a zero-dimensional quotient -/

/-- **`dim_k H⁰(X, 𝒬) = χ(X, ℱ) - χ(X, ω)`** for a short exact sequence
`0 ⟶ ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` of coherent modules on `X` whose quotient has zero-dimensional support.

The Euler characteristic is additive ([Stacks, Tag 08AA]), so `χ(X, 𝒬) = χ(X, ℱ) - χ(X, ω)`;
and `χ(X, 𝒬) = dim_k H⁰(X, 𝒬)`, because `H¹(X, 𝒬)` vanishes on a coherent module with
zero-dimensional support — the vanishing clause of [Stacks, Tag 0B3J] — and everything above
degree one vanishes by [Stacks, Tag 02UZ].

This is the count `dim_k H⁰(X, 𝒬) = deg(ℒ)` of the field
`AlgebraicGeometry.CohenMacaulayCurveSituation.VanishingSectionData.finrank_cohomology_zero`,
reduced to a difference of Euler characteristics; see the module documentation for what
[Stacks, Tag 0AYV] then evaluates that difference as. -/
public theorem finrank_cohomologyOverField_zero_eq_eulerCharacteristic_sub
    {T : ShortComplex S.X.Modules} [T.X₁.IsCoherent] [T.X₂.IsCoherent] [T.X₃.IsCoherent]
    (hT : T.ShortExact) (hdim : topologicalKrullDim (SheafOfModules.supp T.X₃) ≤ 0) :
    (Module.finrank S.k (cohomologyOverField S.k S.f T.X₃ 0) : ℤ) =
      eulerCharacteristic S.k S.f T.X₂ - eulerCharacteristic S.k S.f T.X₁ := by
  have hone : Module.finrank S.k (cohomologyOverField S.k S.f T.X₃ 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero
      (isZero_firstCohomology_of_supp_dim_le_zero ‹T.X₃.IsCoherent› hdim)
    Module.finrank_zero_of_subsingleton
  have hadd := eulerCharacteristic_add_of_shortExact S.k S.f hT
  have hthree := eulerCharacteristic_eq_sub_finrank (S := S) T.X₃
  rw [hone] at hthree
  omega

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
