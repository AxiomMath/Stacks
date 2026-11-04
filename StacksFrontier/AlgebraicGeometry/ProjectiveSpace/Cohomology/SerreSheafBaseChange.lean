module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafBaseChange.CechRefinement
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafBaseChange.FMapCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafBaseChange.TwistBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafBaseChange.ZeroDim

/-!
# Base change on the cohomology of the twists of projective space

Let `φ : R → S` be a ring map, `n ≥ 0`, and `g : ℙⁿ_S → ℙⁿ_R` the induced morphism, with
`g^* 𝒪(d) = 𝒪(d)`. The pullback map `Hᵖ(ℙⁿ_R, 𝒪(d)) → Hᵖ(ℙⁿ_S, 𝒪(d))` (the composite of
`Hᵖ(ℙⁿ_R, 𝒪(d)) → Hᵖ(ℙⁿ_R, g_* 𝒪(d))` with the map `Hᵖ(ℙⁿ_R, g_* 𝒪(d)) → Hᵖ(ℙⁿ_S, 𝒪(d))` of
[Stacks, Tag 01FD]) is compatible, through Equation [Stacks, Tag 01XU], with the coefficientwise
maps `R[T₀, …, Tₙ]_d → S[T₀, …, Tₙ]_d` on `H⁰` and with the base change of `R`-linear forms on
`(R[T₀, …, Tₙ])_{-n-1-d}` on `Hⁿ` ([Stacks, Tag 01XV]).

The pullback map is computed on Čech cochains for the standard coverings: the covering of `ℙⁿ_S` by
the `D₊(Tᵢ)` refines the pullback of that of `ℙⁿ_R`, and on the charts the pullback is the map of
localizations `R[T₀, …, Tₙ]_{(T_I)} → S[T₀, …, Tₙ]_{(T_I)}` induced by `φ`.

For `n = 0`, Equation [Stacks, Tag 01XU] fails: `ℙ⁰_R = Spec R`, so `H⁰(ℙ⁰_R, 𝒪(d)) = R` for
every `d`, whereas `R[T₀]_d = 0` for `d < 0` and `Hom_R(R[T₀]_{-1-d}, R) = 0` for `d ≥ 0`. Over a
nonzero ring both identifications are therefore impossible for suitable `d`. The correct statement
uses [Stacks, Tag 01XT], which for `n = 0` reads `H⁰(ℙ⁰_R, 𝒪(d)) = R[T₀]_d` for `d ≥ 0` and
`H⁰(ℙ⁰_R, 𝒪(d)) = (T₀⁻¹ R[T₀⁻¹])_d ≅ Hom_R(R[T₀]_{-1-d}, R)` for `d < 0`; in these ranges
multiplication and base change act as for `n ≥ 1`.

## Main results

* `Stacks.Cohomology.CechIso.fMapCohomology`: the map `Hᵖ(Y, 𝒢) → Hᵖ(X, ℱ)` attached to a
  morphism of ringed spaces `g : X → Y` and an `𝒪_Y`-linear map `𝒢 → g_* ℱ`.
* `Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology_degreeZero_baseChange` and
  `serreTwistCohomology_degreeTop_baseChange`: base change on `H⁰` and on `Hⁿ`, `n ≥ 1`.
* `Stacks.ProjectiveSpace.Cohomology.not_nonempty_twistCohomology_zeroDim_iso_twistChart_empty`
  and `not_nonempty_twistCohomology_zeroDim_iso_dual`: Equation [Stacks, Tag 01XU] fails for
  `n = 0` over a nonzero ring.
* `Stacks.ProjectiveSpace.Cohomology.zeroDim_degreeZero_mul`, `zeroDim_degreeTop_mul`,
  `zeroDim_degreeZero_baseChange`, `zeroDim_degreeTop_baseChange`: the statements for `n = 0`.

-/
