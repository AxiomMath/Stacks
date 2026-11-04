module

public import StacksFrontier.RingTheory.DeRham.LogPolesRestriction
public import StacksFrontier.RingTheory.DeRham.PolynomialQuasiIso

/-!
# The differential of the forms with log poles, in the equation-free model

Let `A → R` be a ring map and let `t ∈ R` cut out a divisor `Y = Spec (R ⧸ (t))` in
`X = Spec R`. [Stacks, Tag 0FMW] makes `Ω^•_{X/S}(log Y)` a complex; this file proves the
algebraic fact that its differential exists, in the form the *equation-free* presentation
`AlgebraicGeometry.Scheme.Hom.logPolesForms` of
`StacksFrontier/AlgebraicGeometry/DeRham/LogPoles/FormsSheaf.lean` needs.

In that presentation a log form of degree `p` is an `𝒪_X`-linear map `φ : ℐ → 𝒦^p`, where `ℐ` is
the ideal sheaf of `Y` and `𝒦^p` the forms restricting to zero on `Y`; where `ℐ = (t)` it is the
form `φ(t)/t`. Differentiating that form and multiplying back by `t` gives

`t · d(φ(t)/t) = d(φ(t)) - t⁻¹ dt ∧ φ(t)`,

so the value of the differential at `t` is the form `ξ` solving

`t · ξ = t · d ζ - dt ∧ ζ`,  `ζ = φ(t)`,

an equation with no `t⁻¹` in it. This file proves that `ξ` exists, that it again restricts to
zero on `Y` — so that the differential lands in `𝒦^{p+1}` and the construction can be iterated —
and that `ξ` is unique as soon as multiplication by `t` is injective on the forms, which is
condition (2) of [Stacks, Tag 0FMV].

## Main results

* `Stacks.LogPoles.exists_logDifferential`: **the differential exists.** For a form `ζ` of any
  degree restricting to zero on the divisor there is a form `ξ` of one degree higher, again
  restricting to zero, with `t · ξ = t · d ζ - dt ∧ ζ`.
* `Stacks.LogPoles.existsUnique_logDifferential`: it is the unique such form when multiplication
  by `t` is injective on the forms.

## Implementation notes

The equation is stated as `t • ξ = t • d ζ - dt ∧ ζ` rather than as `ξ = d ζ - dlog t ∧ ζ`:
nothing is localized, no module of forms with a pole is used, and the hypothesis of
[Stacks, Tag 0FMV] enters only to make `ξ` unique. That is also why the existence statement
carries no regularity hypothesis at all.

The proof is the computation the source performs. A form restricting to zero on the divisor is
`ζ = dt ∧ η + t ω` by `Stacks.LogPoles.ker_mapExteriorPower_quotient_succ` together with
`Stacks.LogPoles.logSubmodule_span_singleton` (in degree zero `ζ = t ω` by
`Stacks.LogPoles.ker_mapExteriorPower_quotient_zero`), and then

`d ζ = dt ∧ ω + t · d ω - dt ∧ d η`,  `dt ∧ ζ = t · (dt ∧ ω)`,

by the Leibniz rule `KaehlerDifferential.deRhamDifferential_smul`, the anticommutation
`KaehlerDifferential.deRhamDifferential_wedgeLeft_D` and `exteriorPower.wedgeLeft_wedgeLeft`, so
that `t · d ζ - dt ∧ ζ = t · (t · d ω - dt ∧ d η)` and `ξ = t · d ω - dt ∧ d η`. Both summands of
`ξ` are visibly in the logarithmic submodule, which is what keeps the differential inside `𝒦`.

The degree-zero case is not a degenerate one: there `𝒦^0` is the ideal `(t)` rather than the
logarithmic submodule, so the decomposition of `ζ` has no `dt ∧ η` summand and `ξ = t · d ω`.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), whose complex this is
  the differential of
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), whose condition (2)
  makes the differential unique
* [Stacks Project, Tag 0FUA](https://stacks.math.columbia.edu/tag/0FUA), the complex of log poles
-/

@[expose] public noncomputable section

open KaehlerDifferential

universe u

namespace Stacks.LogPoles

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-- A multiple of `t` restricts to zero on the divisor in positive degree. -/
private theorem mapExteriorPower_quotient_succ_smul (t : R) (p : ℕ) (x : ⋀[R]^(p + 1) (Ω[R⁄A])) :
    KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) (p + 1) (t • x) = 0 := by
  rw [← LinearMap.mem_ker, ker_mapExteriorPower_quotient_succ, logSubmodule_span_singleton]
  exact Submodule.mem_sup_right
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) trivial)

/-- **The differential of a log form exists.** Let `t ∈ R` cut out the divisor and let `ζ` be a
`p`-form restricting to zero on it. Then there is a `(p + 1)`-form `ξ`, again restricting to
zero on the divisor, with

`t · ξ = t · d ζ - dt ∧ ζ`.

Where `ℐ = (t)` and `ζ = φ(t)` for a log form `φ : ℐ → 𝒦^p`, this `ξ` is the value at `t` of the
differential of `φ`: it is `t · d(ζ/t)`, computed without inverting `t`. -/
theorem exists_logDifferential (t : R) (p : ℕ) {ζ : ⋀[R]^p (Ω[R⁄A])}
    (hζ : KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) p ζ = 0) :
    ∃ ξ : ⋀[R]^(p + 1) (Ω[R⁄A]),
      KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) (p + 1) ξ = 0 ∧
        t • ξ = t • deRhamDifferential (A := A) p ζ -
          exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p ζ := by
  cases p with
  | zero =>
      rw [← LinearMap.mem_ker, ker_mapExteriorPower_quotient_zero] at hζ
      obtain ⟨ω, rfl⟩ := exists_smul_of_mem_span_singleton_smul_top t hζ
      refine ⟨t • deRhamDifferential (A := A) 0 ω, ?_, ?_⟩
      · exact mapExteriorPower_quotient_succ_smul t 0 _
      · rw [deRhamDifferential_smul, map_smul]
        module
  | succ q =>
      rw [← LinearMap.mem_ker, ker_mapExteriorPower_quotient_succ,
        logSubmodule_span_singleton] at hζ
      obtain ⟨a, ⟨η, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp hζ
      obtain ⟨ω, rfl⟩ := exists_smul_of_mem_span_singleton_smul_top t hb
      refine ⟨t • deRhamDifferential (A := A) (q + 1) ω -
        exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) (q + 1)
          (deRhamDifferential (A := A) q η), ?_, ?_⟩
      · rw [map_sub, mapExteriorPower_quotient_succ_smul, zero_sub, neg_eq_zero,
          ← LinearMap.mem_ker, ker_mapExteriorPower_quotient_succ, logSubmodule_span_singleton]
        exact Submodule.mem_sup_left ⟨_, rfl⟩
      · rw [map_add, deRhamDifferential_wedgeLeft_D, deRhamDifferential_smul, map_add,
          exteriorPower.wedgeLeft_wedgeLeft, map_smul]
        module

/-- **The differential of a log form is unique** when multiplication by `t` is injective on the
forms, which is condition (2) of [Stacks, Tag 0FMV]: the equation `t · ξ = t · d ζ - dt ∧ ζ`
determines `ξ`. This is what makes the differential of
`AlgebraicGeometry.Scheme.Hom.logPolesForms` well defined. -/
theorem existsUnique_logDifferential {t : R} (p : ℕ)
    (ht : IsSMulRegular (↥(⋀[R]^(p + 1) (Ω[R⁄A]))) t) {ζ : ⋀[R]^p (Ω[R⁄A])}
    (hζ : KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) p ζ = 0) :
    ∃! ξ : ⋀[R]^(p + 1) (Ω[R⁄A]),
      KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) (p + 1) ξ = 0 ∧
        t • ξ = t • deRhamDifferential (A := A) p ζ -
          exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p ζ := by
  obtain ⟨ξ, hker, heq⟩ := exists_logDifferential t p hζ
  exact ⟨ξ, ⟨hker, heq⟩, fun ξ' hξ' => ht (hξ'.2.trans heq.symm)⟩

end Stacks.LogPoles

end
