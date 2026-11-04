module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Algebra.Polynomial.Expand
public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham complex of the affine line in positive characteristic

The Poincaré lemma for a polynomial algebra — the inclusion `Ω^•_{A/R} → Ω^•_{A[X]/R}` is a
quasi-isomorphism — is `PolynomialDeRham.quasiIso_incl`, under the hypothesis that `A` contains
`ℚ`.  This file shows that the hypothesis cannot be dropped.

Everything rests on one identification, valid over any commutative ring `A`: the de Rham complex
`Ω^•_{A[X]/A}` of the affine line over `A` is concentrated in degrees `0` and `1`, both terms are
free of rank one — on `1` and on `dX` — and the only differential is `Polynomial.derivative`.
Read on the monomial basis this is the direct sum of complexes
`A ⊕ ⨁_{n ≥ 1} (A · Xⁿ --n--> A · X^{n-1} dX)`.

If now `k` is a field of characteristic `p > 0`, the `n`-th summand has zero differential whenever
`p ∣ n`, and three things follow.  The differential is not surjective, since `X^{p-1}` is not a
derivative; hence `Ω^•_{k[X]/k}` is not exact in degree `1`, while the de Rham complex of the base
`Ω^•_{k/k}` vanishes in degree `1` outright; hence `PolynomialDeRham.incl k k` is not a
quasi-isomorphism.  Moreover `ker (d : Ω^0 → Ω^1)` contains the image of `Polynomial.expand k p`
and the quotient `Ω^1 / im (d)` receives `X^{p-1} · expand k p (·)` injectively, so both
`H^0_{dR}(𝐀^1_k/k)` and `H^1_{dR}(𝐀^1_k/k)` are infinite dimensional over `k`.

## Main results

* `PolynomialDeRham.polynomialEquiv_oneEquiv_deRhamDifferential_zero`: the degree-zero
  differential of `Ω^•_{A[X]/A}` is `Polynomial.derivative`, read through `⋀^0 ≅ A[X]` and
  `⋀^1 ≅ Ω[A[X]⁄A] ≅ A[X]`.
* `PolynomialDeRham.polynomialEquiv_oneEquiv_deRhamDifferential_zero_X_pow`: on monomials it is
  `Xⁿ ↦ n X^{n-1} dX`, which is the displayed decomposition.
* `PolynomialDeRham.surjective_deRhamDifferential_zero_iff`: that differential is surjective
  exactly when `Polynomial.derivative` is.
* `PolynomialDeRham.not_surjective_deRhamDifferential_zero` and
  `PolynomialDeRham.not_exactAt_one_deRhamComplex_polynomial`: in characteristic `p > 0` the
  differential is not surjective and `Ω^•_{k[X]/k}` is not exact in degree one.
* `PolynomialDeRham.not_quasiIso_incl`: in characteristic `p > 0` the inclusion
  `Ω^•_{k/k} → Ω^•_{k[X]/k}` is **not** a quasi-isomorphism, so the `ℚ`-algebra hypothesis of the
  Poincaré lemma is necessary.
* `PolynomialDeRham.not_finiteDimensional_ker_deRhamDifferential_zero` and
  `PolynomialDeRham.not_finiteDimensional_deRhamCohomology_one`: in characteristic `p > 0` both
  `H^0_{dR}(𝐀^1_k/k)` and `H^1_{dR}(𝐀^1_k/k)` are infinite dimensional over `k`.

## Implementation notes

`H^0` and `H^1` are spelled as `LinearMap.ker (deRhamDifferential 0)` and as the quotient of
`⋀[k[X]]^1 Ω[k[X]⁄k]` by `LinearMap.range (deRhamDifferential 0)`.  Nothing enters degree zero, so
the first is the degree-zero cohomology on the nose; and `⋀[k[X]]^2 Ω[k[X]⁄k]` vanishes
(`PolynomialDeRham.subsingleton_exteriorPower_polynomial`), so every `1`-form is closed and the
second is the degree-one cohomology on the nose.

Stacks 0FUJ introduces the affine line as `Spec(k[x])` and then writes the displayed decomposition
in the variable `t`, as `k ⊕ ⨁_{n ≥ 1} (k · tⁿ --n--> k · t^{n-1} dt)`; the two letters denote the
same coordinate.  Here it is `Polynomial.X` throughout.

## References

* [Stacks 0FUJ](https://stacks.math.columbia.edu/tag/0FUJ), the counterexample in positive
  characteristic
* [Stacks 0FUI](https://stacks.math.columbia.edu/tag/0FUI), the Poincaré lemma, which assumes
  `ℚ ⊆ 𝒪_S`
-/

open CategoryTheory Polynomial

@[expose] public section

noncomputable section

namespace PolynomialDeRham

open KaehlerDifferential

universe u

/-! ### The de Rham complex of the affine line -/

section Line

variable (A : Type u) [CommRing A]

/-- The degree-zero differential of `Ω^•_{A[X]/A}` is `Polynomial.derivative`: under the
identifications `⋀^0 Ω[A[X]⁄A] ≅ A[X]` and `⋀^1 Ω[A[X]⁄A] ≅ Ω[A[X]⁄A] ≅ A[X] dX` it sends `g` to
`dg/dX`. -/
theorem polynomialEquiv_oneEquiv_deRhamDifferential_zero (ξ : ⋀[A[X]]^0 (Ω[A[X]⁄A])) :
    polynomialEquiv A (exteriorPower.oneEquiv A[X] (Ω[A[X]⁄A])
        (deRhamDifferential (A := A) 0 ξ)) =
      derivative (exteriorPower.zeroEquiv A[X] (Ω[A[X]⁄A]) ξ) := by
  rw [oneEquiv_deRhamDifferential_zero, polynomialEquiv_D]

/-- **The decomposition of the de Rham complex of the affine line**: on the monomial basis the only
differential of `Ω^•_{A[X]/A}` sends `Xⁿ` to `n X^{n-1} dX`.  Together with
`PolynomialDeRham.subsingleton_exteriorPower_polynomial`, which says the complex stops after degree
one, this is the direct sum `A ⊕ ⨁_{n ≥ 1} (A · Xⁿ --n--> A · X^{n-1} dX)`. -/
@[stacks 0FUJ "the displayed decomposition of the de Rham complex of the affine line: d Xⁿ =
n X^{n-1} dX"]
theorem polynomialEquiv_oneEquiv_deRhamDifferential_zero_X_pow (n : ℕ) :
    polynomialEquiv A (exteriorPower.oneEquiv A[X] (Ω[A[X]⁄A]) (deRhamDifferential (A := A) 0
        ((exteriorPower.zeroEquiv A[X] (Ω[A[X]⁄A])).symm ((X : A[X]) ^ n)))) =
      (n : A[X]) * (X : A[X]) ^ (n - 1) := by
  rw [polynomialEquiv_oneEquiv_deRhamDifferential_zero, LinearEquiv.apply_symm_apply,
    derivative_X_pow, C_eq_natCast]

/-- A degree-zero form `ξ` has differential the `1`-form attached to `f` iff `ξ` has derivative
`f`. -/
private theorem deRhamDifferential_zero_eq_iff (ξ : ⋀[A[X]]^0 (Ω[A[X]⁄A])) (f : A[X]) :
    deRhamDifferential (A := A) 0 ξ =
        (exteriorPower.oneEquiv A[X] (Ω[A[X]⁄A])).symm ((polynomialEquiv A).symm f) ↔
      derivative (exteriorPower.zeroEquiv A[X] (Ω[A[X]⁄A]) ξ) = f := by
  rw [LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply,
    polynomialEquiv_oneEquiv_deRhamDifferential_zero]

/-- The degree-zero de Rham differential of `A[X]` over `A` is surjective exactly when every
polynomial is a derivative. -/
theorem surjective_deRhamDifferential_zero_iff :
    Function.Surjective (deRhamDifferential (A := A) (B := A[X]) 0) ↔
      Function.Surjective (derivative (R := A)) := by
  constructor
  · intro h f
    obtain ⟨ξ, hξ⟩ :=
      h ((exteriorPower.oneEquiv A[X] (Ω[A[X]⁄A])).symm ((polynomialEquiv A).symm f))
    exact ⟨_, (deRhamDifferential_zero_eq_iff A ξ f).mp hξ⟩
  · intro h η
    obtain ⟨q, hq⟩ := h (polynomialEquiv A (exteriorPower.oneEquiv A[X] (Ω[A[X]⁄A]) η))
    refine ⟨(exteriorPower.zeroEquiv A[X] (Ω[A[X]⁄A])).symm q, ?_⟩
    refine (exteriorPower.oneEquiv A[X] (Ω[A[X]⁄A])).injective ((polynomialEquiv A).injective ?_)
    rw [polynomialEquiv_oneEquiv_deRhamDifferential_zero, LinearEquiv.apply_symm_apply, hq]

end Line

/-! ### Positive characteristic -/

section CharP

variable (k : Type u) [Field k] (p : ℕ) [CharP k p]

/-- In characteristic `p` the natural number `p` is zero in `k[X]` too. -/
private theorem natCast_char_polynomial_eq_zero : (p : k[X]) = 0 := by
  rw [← C_eq_natCast, CharP.cast_eq_zero k p, map_zero]

/-- In characteristic `p`, a derivative has vanishing coefficient in every degree `m` with
`p ∣ m + 1`. -/
private theorem coeff_derivative_eq_zero_of_dvd (g : k[X]) {m : ℕ} (hm : p ∣ m + 1) :
    (derivative g).coeff m = 0 := by
  rw [coeff_derivative, ← Nat.cast_add_one, (CharP.cast_eq_zero_iff k p _).mpr hm, mul_zero]

/-- In characteristic `p > 0` not every polynomial is a derivative: the coefficient of `X^{p-1}` in
a derivative is `p` times something, hence zero, while `X^{p-1}` has coefficient `1` there. -/
theorem not_surjective_derivative (hp : p ≠ 0) :
    ¬ Function.Surjective (derivative (R := k)) := by
  intro h
  obtain ⟨g, hg⟩ := h ((X : k[X]) ^ (p - 1))
  have hc := coeff_derivative_eq_zero_of_dvd k p g (m := p - 1) (by rw [Nat.sub_one_add_one hp])
  rw [hg, coeff_X_pow_self] at hc
  exact one_ne_zero hc

/-- In characteristic `p > 0` the degree-zero de Rham differential of `k[X]` over `k` is not
surjective: `X^{p-1} dX` is not exact. -/
theorem not_surjective_deRhamDifferential_zero (hp : p ≠ 0) :
    ¬ Function.Surjective (deRhamDifferential (A := k) (B := k[X]) 0) := fun h ↦
  not_surjective_derivative k p hp ((surjective_deRhamDifferential_zero_iff k).mp h)

/-- In characteristic `p > 0` the de Rham complex of the affine line is not exact in degree one:
`H^1_{dR}(𝐀^1_k/k) ≠ 0`, witnessed by the class of `X^{p-1} dX`. -/
theorem not_exactAt_one_deRhamComplex_polynomial (hp : p ≠ 0) :
    ¬ (deRhamComplex k k[X]).ExactAt 1 := by
  have h2 : Subsingleton (⋀[k[X]]^2 (Ω[k[X]⁄k])) :=
    subsingleton_exteriorPower_polynomial k (p := 2) le_rfl
  intro hex
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (ComplexShape.prev_eq' _ rfl)
    (ComplexShape.next_eq' _ rfl), ShortComplex.moduleCat_exact_iff] at hex
  have h3 : Subsingleton ((((deRhamComplex k k[X]).sc' 0 1 2)).X₃ : Type u) := h2
  refine not_surjective_deRhamDifferential_zero k p hp fun η ↦ ?_
  obtain ⟨ξ, hξ⟩ := hex η (Subsingleton.elim _ _)
  refine ⟨ξ, ?_⟩
  have hξ' : ((deRhamComplex k k[X]).d 0 (0 + 1)).hom ξ = η := hξ
  rwa [deRhamComplex_d] at hξ'

/-- **The Poincaré lemma fails in positive characteristic.**  For a field `k` of characteristic
`p > 0` the inclusion of de Rham complexes `Ω^•_{k/k} → Ω^•_{k[X]/k}` is not a quasi-isomorphism:
the source vanishes in degree one, while the target has `X^{p-1} dX` as a non-exact closed form.
So the hypothesis `ℚ ⊆ A` of `PolynomialDeRham.quasiIso_incl` cannot be dropped.

This is the affine content of Stacks 0FUJ: taking `X = S = Spec(k)` and `L = 𝐀^1_k` in Stacks
0FUI, the map `Ω^•_{X/S} → π_*Ω^•_{L/S}` on global sections is exactly `incl k k`. -/
@[stacks 0FUJ "the counterexample: in characteristic p > 0 the Poincaré lemma 0FUI fails for the
affine line over a field, so its ℚ-algebra hypothesis is necessary"]
theorem not_quasiIso_incl (hp : p ≠ 0) : ¬ QuasiIso (incl k k) := by
  have hΩ : Subsingleton (Ω[k⁄k]) :=
    KaehlerDifferential.subsingleton_of_surjective (R := k) (S := k) fun x ↦ ⟨x, rfl⟩
  have h1 : Subsingleton (⋀[k]^1 (Ω[k⁄k])) :=
    (exteriorPower.oneEquiv k (Ω[k⁄k])).toEquiv.subsingleton
  have h1' : Subsingleton (((deRhamComplex k k).X 1 : ModuleCat.{u} k) : Type u) := h1
  intro h
  have hsrc : (deRhamComplex k k).ExactAt 1 :=
    HomologicalComplex.ExactAt.of_isZero (ModuleCat.isZero_of_subsingleton _)
  exact not_exactAt_one_deRhamComplex_polynomial k p hp
    ((exactAt_iff_of_quasiIsoAt (incl k k) 1).mp hsrc)

/-- In characteristic `p > 0` the closed degree-zero forms on `𝐀^1_k` are infinite dimensional:
`H^0_{dR}(𝐀^1_k/k)` contains every `p`-th power substitution `expand k p f`, because
`d/dX (expand k p f) = expand k p (df/dX) · p X^{p-1} = 0`. -/
@[stacks 0FUJ "H⁰ of the de Rham complex of the affine line is infinite dimensional in
characteristic p > 0"]
theorem not_finiteDimensional_ker_deRhamDifferential_zero (hp : p ≠ 0) :
    ¬ FiniteDimensional k (LinearMap.ker (deRhamDifferential (A := k) (B := k[X]) 0)) := by
  intro hfin
  have hker : ∀ f : k[X],
      ((exteriorPower.zeroEquiv k[X] (Ω[k[X]⁄k])).symm.toLinearMap.restrictScalars k ∘ₗ
        (Polynomial.expand k p).toLinearMap) f ∈
      LinearMap.ker (deRhamDifferential (A := k) (B := k[X]) 0) := by
    intro f
    have h0 := (deRhamDifferential_zero_eq_iff k
      ((exteriorPower.zeroEquiv k[X] (Ω[k[X]⁄k])).symm (Polynomial.expand k p f)) 0).mpr (by
        rw [LinearEquiv.apply_symm_apply, derivative_expand, natCast_char_polynomial_eq_zero,
          zero_mul, mul_zero])
    simpa only [map_zero, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply] using h0
  refine Module.not_finite_of_infinite_basis (Polynomial.basisMonomials k)
    (FiniteDimensional.of_injective
      (V₂ := ↥(LinearMap.ker (deRhamDifferential (A := k) (B := k[X]) 0)))
      (LinearMap.codRestrict (LinearMap.ker (deRhamDifferential (A := k) (B := k[X]) 0))
        ((exteriorPower.zeroEquiv k[X] (Ω[k[X]⁄k])).symm.toLinearMap.restrictScalars k ∘ₗ
          (Polynomial.expand k p).toLinearMap) hker) ?_)
  intro f g hfg
  have h := Subtype.ext_iff.mp hfg
  simp only [LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply] at h
  exact Polynomial.expand_injective (Nat.pos_of_ne_zero hp)
    ((exteriorPower.zeroEquiv k[X] (Ω[k[X]⁄k])).symm.injective h)

/-- In characteristic `p > 0` the degree-one de Rham cohomology of `𝐀^1_k` is infinite dimensional:
`f ↦ [expand k p f · X^{p-1} dX]` is an injective `k`-linear map out of `k[X]`, because the
coefficient of a derivative in every degree `≡ -1 mod p` vanishes. -/
@[stacks 0FUJ "H¹ of the de Rham complex of the affine line is infinite dimensional in
characteristic p > 0"]
theorem not_finiteDimensional_deRhamCohomology_one (hp : p ≠ 0) :
    ¬ FiniteDimensional k (↥(⋀[k[X]]^1 (Ω[k[X]⁄k])) ⧸
      LinearMap.range (deRhamDifferential (A := k) (B := k[X]) 0)) := by
  intro hfin
  refine Module.not_finite_of_infinite_basis (Polynomial.basisMonomials k)
    (FiniteDimensional.of_injective
      ((LinearMap.range (deRhamDifferential (A := k) (B := k[X]) 0)).mkQ ∘ₗ
        (exteriorPower.oneEquiv k[X] (Ω[k[X]⁄k])).symm.toLinearMap.restrictScalars k ∘ₗ
        (polynomialEquiv k).symm.toLinearMap.restrictScalars k ∘ₗ
        LinearMap.mulRight k ((X : k[X]) ^ (p - 1)) ∘ₗ
        (Polynomial.expand k p).toLinearMap) ?_)
  rw [injective_iff_map_eq_zero]
  intro f hf
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply,
    Submodule.mkQ_apply] at hf
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hf
  obtain ⟨ξ, hξ⟩ := hf
  have hkey := (deRhamDifferential_zero_eq_iff k ξ _).mp hξ
  refine Polynomial.ext fun n ↦ ?_
  have hc := coeff_derivative_eq_zero_of_dvd k p
    (exteriorPower.zeroEquiv k[X] (Ω[k[X]⁄k]) ξ) (m := p * n + (p - 1))
    ⟨n + 1, by rw [Nat.add_assoc, Nat.sub_one_add_one hp, Nat.mul_succ]⟩
  rw [hkey] at hc
  rw [Polynomial.coeff_mul_X_pow, Polynomial.coeff_expand_mul' (Nat.pos_of_ne_zero hp)] at hc
  exact hc.trans (Polynomial.coeff_zero n).symm

end CharP

end PolynomialDeRham
