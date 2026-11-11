module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.HomogeneousQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegreClosedImmersion
public import StacksFrontier.Examples.Scheme.NoetherianSpaceNotNoetherianRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Non-finite `H⁰` of a projective scheme

Stacks Tag 0HAT: there exist a ring `R` and a projective scheme `X` over `R` such that
`H⁰(X, 𝒪_X)` is not a finite `R`-module, and a quasi-coherent module `𝓕` of finite type on
`𝐏¹_R` such that `H⁰(𝐏¹_R, 𝓕)` is not a finite `R`-module.

The construction is the one of the source (Examples, Section "Nonfinite cohomology of the
structure sheaf of a projective scheme"). Let `I` be an ideal of `R` that is not finitely
generated, let `S = R[x, y] / x y I`, graded with `x` and `y` in degree one, and let
`X = Proj S`. The surjection `R[x, y] → S` makes `X` a closed subscheme of `𝐏¹_R`, and `𝓕` is
`i_* 𝒪_X` for that closed immersion `i`. The source identifies `H⁰(X, 𝒪_X)` with the module
`M = {(F, G) ∈ R² | F - G ∈ I}`, which surjects onto `I` by `(F, G) ↦ F - G`.

The formal proof uses only that surjection. A global function `s` on `X` pulls back to the two
standard charts `Spec S_(x)` and `Spec S_(y)`; evaluating at the points `[1 : 0]` and `[0 : 1]`
gives two elements of `R`, and their difference is an `R`-linear map
`Stacks.Examples.NonfiniteGlobalSections.constantTermDifference : H⁰(X, 𝒪_X) → R`.

* Its values lie in `I`
  (`Stacks.Examples.NonfiniteGlobalSections.constantTermDifference_mem`). Modulo `I` the two
  chart rings become `(R/I)[t]` and `(R/I)[t⁻¹]` and agree in `(R/I)[t, t⁻¹]` after inverting
  `x y`, so their constant terms agree: this is the constancy of global functions on `𝐏¹_{R/I}`,
  proved here by comparing coefficients of Laurent polynomials
  (`Stacks.Examples.NonfiniteGlobalSections.constX_sub_constY_mem`).
* Every `a ∈ I` is a value
  (`Stacks.Examples.NonfiniteGlobalSections.exists_constantTermDifference_eq`): the function
  equal to `a` on `D₊(x)` and to `0` on `D₊(y)` glues, because `a x y = 0` in `S`.

So if `H⁰(X, 𝒪_X)` were finite over `R`, its image `I` would be finitely generated. The same map
applies to `H⁰(𝐏¹_R, i_* 𝒪_X)`, which is `H⁰(X, 𝒪_X)` with the `R`-module structure transported
along `i`.

The ring used for the existence statements is `k[x₀, x₁, …]/(x₀², x₁², …)` over `k = ℚ`, whose
ideal of variables is not finitely generated
(`Stacks.Examples.infiniteSquareZeroVariableIdeal_not_fg`, Stacks Tag 0G62).

## Main definitions

* `Stacks.Examples.NonfiniteGlobalSections.pinchScheme`: the scheme `X = Proj(R[x, y] / x y I)`.
* `Stacks.Examples.NonfiniteGlobalSections.pinchToSpec`: its structure morphism `X ⟶ Spec R`.
* `Stacks.Examples.NonfiniteGlobalSections.pinchToProjectiveLine`: the closed immersion
  `X ⟶ 𝐏¹_R`.
* `Stacks.Examples.NonfiniteGlobalSections.pinchSheaf`: the module `i_* 𝒪_X` on `𝐏¹_R`.

## Main results

* `Stacks.Examples.NonfiniteGlobalSections.isProjective_pinchToSpec` and
  `Stacks.Examples.NonfiniteGlobalSections.isProjectiveMorphism_pinchToSpec`: `X` is projective
  over `R`, in the sense of Tag 01W8 and in the H-projective sense.
* `Stacks.Examples.NonfiniteGlobalSections.not_finite_structureHom`: for any `R` and any ideal
  `I` that is not finitely generated, `H⁰(X, 𝒪_X)` is not a finite `R`-module.
* `Stacks.Examples.NonfiniteGlobalSections.not_finite_pinchSheaf`: likewise for
  `H⁰(𝐏¹_R, i_* 𝒪_X)`, where `i_* 𝒪_X` is quasi-coherent of finite type.
* `Stacks.Examples.exists_projective_not_finite_globalSections`: **Stacks Tag 0HAT**, both
  existence statements.

## Implementation notes

`H⁰` is the module of global sections. For `𝒪_X` it is the ring `Γ(X, 𝒪_X)`, an `R`-module
through `R ≅ Γ(Spec R, 𝒪) → Γ(X, 𝒪_X)`, and finiteness is `RingHom.Finite` of that ring map; for
`𝓕` on `𝐏¹_R` it is `Γ(𝐏¹_R, 𝓕)`, a `Γ(𝐏¹_R, 𝒪)`-module, with scalars restricted along the
structure morphism. Projective space `𝐏¹_R` is the library's
`AlgebraicGeometry.projectiveSpaceOverRing 1 R`, the base change of `𝐏¹_ℤ`; the closed immersion
is built in the polynomial model `Proj R[x, y]` and transported along
`Stacks.ProjectiveCohomology.projModelIso`.

## References

* [Stacks Project, Tag 0HAT](https://stacks.math.columbia.edu/tag/0HAT)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 0G62](https://stacks.math.columbia.edu/tag/0G62)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial

universe u

namespace Stacks.Examples.NonfiniteGlobalSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### The graded ring `S = R[x, y] / x y I` -/

/-- The generators `x y a`, `a ∈ I`, of the ideal `x y I` of `R[x, y]`. -/
def pinchGenerators : Set (MvPolynomial (Fin 2) R) :=
  {p | ∃ a ∈ I, p = X 0 * X 1 * C a}

theorem isHomogeneousElem_of_mem_pinchGenerators {p : MvPolynomial (Fin 2) R}
    (hp : p ∈ pinchGenerators I) :
    SetLike.IsHomogeneousElem (homogeneousSubmodule (Fin 2) R) p := by
  obtain ⟨a, -, rfl⟩ := hp
  refine ⟨2, ?_⟩
  rw [mem_homogeneousSubmodule]
  have h0 : (X 0 : MvPolynomial (Fin 2) R).IsHomogeneous 1 := isHomogeneous_X R 0
  have h1 : (X 1 : MvPolynomial (Fin 2) R).IsHomogeneous 1 := isHomogeneous_X R 1
  simpa using (h0.mul h1).mul (isHomogeneous_C (Fin 2) a)

/-- The homogeneous ideal `x y I` of `R[x, y]`. -/
def pinchIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin 2) R) where
  toSubmodule := Ideal.span (pinchGenerators I)
  is_homogeneous' :=
    Ideal.homogeneous_span _ _ fun _ hp => isHomogeneousElem_of_mem_pinchGenerators I hp

/-- The ring `S = R[x, y] / x y I`. -/
abbrev PinchRing : Type u := MvPolynomial (Fin 2) R ⧸ (pinchIdeal I).toIdeal

/-- The grading of `S = R[x, y] / x y I` with `x` and `y` of degree one. -/
abbrev pinchGrading : ℕ → Submodule R (PinchRing I) :=
  RingTheory.HomogeneousQuotient.quotientGrading (homogeneousSubmodule (Fin 2) R) (pinchIdeal I)

/-- The class of `x` in `S`. -/
abbrev coordX : PinchRing I := Ideal.Quotient.mk _ (X 0)

/-- The class of `y` in `S`. -/
abbrev coordY : PinchRing I := Ideal.Quotient.mk _ (X 1)

theorem coordX_mem : coordX I ∈ pinchGrading I 1 :=
  RingTheory.HomogeneousQuotient.quotientGrading_mk_mem _ _ (by
    rw [mem_homogeneousSubmodule]; exact isHomogeneous_X R 0)

theorem coordY_mem : coordY I ∈ pinchGrading I 1 :=
  RingTheory.HomogeneousQuotient.quotientGrading_mk_mem _ _ (by
    rw [mem_homogeneousSubmodule]; exact isHomogeneous_X R 1)

theorem coordXY_mem : coordX I * coordY I ∈ pinchGrading I 2 :=
  SetLike.mul_mem_graded (coordX_mem I) (coordY_mem I)

theorem coordX_mul_coordY_mul_C {a : R} (ha : a ∈ I) :
    coordX I * coordY I * Ideal.Quotient.mk _ (C a) = 0 := by
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨a, ha, rfl⟩

/-- A ring homomorphism out of `S`, determined by a ring homomorphism out of `R` and the images
of `x` and `y`, which must kill `x y I`. -/
def pinchLift {T : Type*} [CommRing T] (g : R →+* T) (v : Fin 2 → T)
    (hv : ∀ a ∈ I, v 0 * v 1 * g a = 0) : PinchRing I →+* T :=
  Ideal.Quotient.lift _ (eval₂Hom g v) fun p hp => by
    refine (Ideal.span_le (I := RingHom.ker (eval₂Hom g v))).mpr ?_ hp
    rintro _ ⟨a, ha, rfl⟩
    simpa using hv a ha

@[simp]
theorem pinchLift_mk {T : Type*} [CommRing T] (g : R →+* T) (v : Fin 2 → T)
    (hv : ∀ a ∈ I, v 0 * v 1 * g a = 0) (p : MvPolynomial (Fin 2) R) :
    pinchLift I g v hv (Ideal.Quotient.mk _ p) = eval₂ g v p := rfl

theorem pinchLift_coordX {T : Type*} [CommRing T] (g : R →+* T) (v : Fin 2 → T)
    (hv : ∀ a ∈ I, v 0 * v 1 * g a = 0) : pinchLift I g v hv (coordX I) = v 0 := by
  simp

theorem pinchLift_coordY {T : Type*} [CommRing T] (g : R →+* T) (v : Fin 2 → T)
    (hv : ∀ a ∈ I, v 0 * v 1 * g a = 0) : pinchLift I g v hv (coordY I) = v 1 := by
  simp

theorem pinchRing_hom_ext {T : Type*} [CommRing T] {φ ψ : PinchRing I →+* T}
    (hC : ∀ r, φ (Ideal.Quotient.mk _ (C r)) = ψ (Ideal.Quotient.mk _ (C r)))
    (hx : φ (coordX I) = ψ (coordX I)) (hy : φ (coordY I) = ψ (coordY I)) : φ = ψ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => hC r) fun i => ?_)
  fin_cases i
  · exact hx
  · exact hy

/-! ### Evaluating degree-zero fractions -/

section AwayEval

variable {T : Type*} [CommRing T]

/-- A ring homomorphism `g : S → T` inverting the homogeneous element `f` induces a ring
homomorphism `S_(f) → T` on the degree-zero localization. -/
def awayEval (f : PinchRing I) (g : PinchRing I →+* T) (hg : IsUnit (g f)) :
    Away (pinchGrading I) f →+* T :=
  (IsLocalization.Away.lift f hg).comp (algebraMap _ (Localization.Away f))

theorem awayEval_mk_mul {f : PinchRing I} {d : ℕ} (hf : f ∈ pinchGrading I d)
    (g : PinchRing I →+* T) (hg : IsUnit (g f)) (n : ℕ) (a : PinchRing I)
    (ha : a ∈ pinchGrading I (n • d)) :
    awayEval I f g hg (Away.mk _ hf n a ha) * g f ^ n = g a := by
  have h := congrArg (IsLocalization.Away.lift f hg)
    (IsLocalization.mk'_spec (Localization.Away f) a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f))
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, map_pow] at h
  simpa [awayEval, Localization.mk_eq_mk'] using h

theorem awayEval_fromZeroRingHom (f : PinchRing I) (g : PinchRing I →+* T) (hg : IsUnit (g f))
    (a : pinchGrading I 0) :
    awayEval I f g hg (fromZeroRingHom _ _ a) = g a := by
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply]
  change IsLocalization.Away.lift f hg (algebraMap _ _ (a : PinchRing I)) = g a
  exact IsLocalization.lift_eq _ _

theorem comp_awayEval {T' : Type*} [CommRing T'] (h : T →+* T') (f : PinchRing I)
    (g : PinchRing I →+* T) (hg : IsUnit (g f)) :
    h.comp (awayEval I f g hg) = awayEval I f (h.comp g) (hg.map h) := by
  have : h.comp (IsLocalization.Away.lift f hg) =
      IsLocalization.Away.lift (S := Localization.Away f) f (g := h.comp g) (hg.map h) :=
    IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun b => by
      simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq])
  rw [awayEval, awayEval, ← RingHom.comp_assoc, this]

theorem awayEval_awayMap {f f' x : PinchRing I} {e : ℕ} (hf' : f' ∈ pinchGrading I e)
    (hx : x = f * f') (g : PinchRing I →+* T) (hg : IsUnit (g x)) (hgf : IsUnit (g f)) :
    (awayEval I x g hg).comp (awayMap _ hf' hx) = awayEval I f g hgf := by
  ext a
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, val_awayMap]
  rw [← RingHom.comp_apply]
  congr 1
  refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun b => ?_)
  simp only [RingHom.comp_apply, Localization.awayLift, IsLocalization.Away.lift_eq]

theorem awayEval_congr (f : PinchRing I) {g g' : PinchRing I →+* T} (h : g = g')
    (hg : IsUnit (g f)) : awayEval I f g hg = awayEval I f g' (h ▸ hg) := by
  subst h
  rfl

end AwayEval

/-! ### The constant terms at the two points `x = 0` and `y = 0` -/

/-- Evaluation `S → R` at the point `[1 : 0]`: `x ↦ 1`, `y ↦ 0`. -/
def evalX : PinchRing I →+* R :=
  pinchLift I (RingHom.id R) ![1, 0] fun a _ => by simp

/-- Evaluation `S → R` at the point `[0 : 1]`: `x ↦ 0`, `y ↦ 1`. -/
def evalY : PinchRing I →+* R :=
  pinchLift I (RingHom.id R) ![0, 1] fun a _ => by simp

theorem isUnit_evalX : IsUnit (evalX I (coordX I)) := by
  simp [evalX]

theorem isUnit_evalY : IsUnit (evalY I (coordY I)) := by
  simp [evalY]

/-- The value at `[1 : 0]` of a degree-zero fraction with denominator a power of `x`. -/
abbrev constX : Away (pinchGrading I) (coordX I) →+* R := awayEval I _ (evalX I) (isUnit_evalX I)

/-- The value at `[0 : 1]` of a degree-zero fraction with denominator a power of `y`. -/
abbrev constY : Away (pinchGrading I) (coordY I) →+* R := awayEval I _ (evalY I) (isUnit_evalY I)

section Laurent

open LaurentPolynomial

/-- `S → (R/I)[t]`, `x ↦ 1`, `y ↦ t`: the chart `x ≠ 0` read modulo `I`. -/
def polyX : PinchRing I →+* Polynomial (R ⧸ I) :=
  pinchLift I (Polynomial.C.comp (Ideal.Quotient.mk I)) ![1, Polynomial.X] fun a ha => by
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]

/-- `S → (R/I)[s]`, `x ↦ s`, `y ↦ 1`: the chart `y ≠ 0` read modulo `I`. -/
def polyY : PinchRing I →+* Polynomial (R ⧸ I) :=
  pinchLift I (Polynomial.C.comp (Ideal.Quotient.mk I)) ![Polynomial.X, 1] fun a ha => by
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]

/-- `S → (R/I)[t, t⁻¹]`, `x ↦ 1`, `y ↦ t`. -/
def laurentX : PinchRing I →+* (R ⧸ I)[T;T⁻¹] :=
  pinchLift I (LaurentPolynomial.C.comp (Ideal.Quotient.mk I)) ![1, T 1] fun a ha => by
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]

/-- `S → (R/I)[t, t⁻¹]`, `x ↦ t⁻¹`, `y ↦ 1`. -/
def laurentY : PinchRing I →+* (R ⧸ I)[T;T⁻¹] :=
  pinchLift I (LaurentPolynomial.C.comp (Ideal.Quotient.mk I)) ![T (-1), 1] fun a ha => by
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]

theorem isUnit_polyX : IsUnit (polyX I (coordX I)) := by simp [polyX]

theorem isUnit_polyY : IsUnit (polyY I (coordY I)) := by simp [polyY]

theorem laurentX_coordXY : laurentX I (coordX I * coordY I) = T 1 := by simp [laurentX]

theorem laurentY_coordXY : laurentY I (coordX I * coordY I) = T (-1) := by simp [laurentY]

theorem isUnit_laurentX : IsUnit (laurentX I (coordX I * coordY I)) := by
  rw [laurentX_coordXY]; exact isUnit_T 1

theorem isUnit_laurentY : IsUnit (laurentY I (coordX I * coordY I)) := by
  rw [laurentY_coordXY]; exact isUnit_T (-1)

theorem isUnit_laurentX_coordX : IsUnit (laurentX I (coordX I)) := by simp [laurentX]

theorem isUnit_laurentY_coordY : IsUnit (laurentY I (coordY I)) := by simp [laurentY]

/-- The automorphism `t ↦ t⁻¹` of `(R/I)[t, t⁻¹]`, as a ring homomorphism. -/
def invertHom : (R ⧸ I)[T;T⁻¹] →+* (R ⧸ I)[T;T⁻¹] := (invert (R := R ⧸ I)).toAlgHom.toRingHom

@[simp]
theorem invertHom_apply (f : (R ⧸ I)[T;T⁻¹]) : invertHom I f = invert f := rfl

theorem toLaurent_comp_polyX : Polynomial.toLaurent.comp (polyX I) = laurentX I :=
  pinchRing_hom_ext I (fun r => by simp [polyX, laurentX, Polynomial.toLaurent_C])
    (by simp [polyX, laurentX]) (by simp [polyX, laurentX, Polynomial.toLaurent_X])

theorem invert_comp_toLaurent_comp_polyY :
    (invertHom I).comp (Polynomial.toLaurent.comp (polyY I)) = laurentY I :=
  pinchRing_hom_ext I (fun r => by simp [polyY, laurentY, Polynomial.toLaurent_C])
    (by simp [polyY, laurentY, Polynomial.toLaurent_X]) (by simp [polyY, laurentY])

theorem evalZero_comp_polyX :
    (Polynomial.evalRingHom 0).comp (polyX I) = (Ideal.Quotient.mk I).comp (evalX I) :=
  pinchRing_hom_ext I (fun r => by simp [polyX, evalX]) (by simp [polyX, evalX])
    (by simp [polyX, evalX])

theorem evalZero_comp_polyY :
    (Polynomial.evalRingHom 0).comp (polyY I) = (Ideal.Quotient.mk I).comp (evalY I) :=
  pinchRing_hom_ext I (fun r => by simp [polyY, evalY]) (by simp [polyY, evalY])
    (by simp [polyY, evalY])

/-- Evaluating a homogeneous polynomial of degree `m` at `a • v` multiplies its value by `aᵐ`. -/
theorem eval₂_mul_of_isHomogeneous {S' ι : Type*} [CommSemiring S'] {R' : Type*}
    [CommSemiring R'] (c : R' →+* S') (a : S') (g : ι → S') {φ : MvPolynomial ι R'} {m : ℕ}
    (hφ : φ.IsHomogeneous m) :
    MvPolynomial.eval₂ c (fun i => a * g i) φ = a ^ m * MvPolynomial.eval₂ c g φ := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : ∑ i ∈ e.support, e i = m := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using hφ (MvPolynomial.mem_support_iff.mp he)
  have hprod : ∏ i ∈ e.support, (a * g i) ^ e i =
      (∏ i ∈ e.support, a ^ e i) * ∏ i ∈ e.support, g i ^ e i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_pow a (g i) (e i)
  rw [hprod, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- On an element of degree `d` the two Laurent evaluations differ by `t⁻ᵈ`. -/
theorem laurentY_of_mem {d : ℕ} {a : PinchRing I} (ha : a ∈ pinchGrading I d) :
    laurentY I a = T (-(d : ℤ)) * laurentX I a := by
  obtain ⟨p, hp, rfl⟩ := (RingTheory.HomogeneousQuotient.mem_quotientGrading_iff _ _).1 ha
  rw [mem_homogeneousSubmodule] at hp
  have hv : (![T (-1), 1] : Fin 2 → (R ⧸ I)[T;T⁻¹]) = fun i => T (-1) * ![1, T 1] i := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mul_one]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← T_add, neg_add_cancel, T_zero]
  simp only [laurentY, laurentX, pinchLift_mk]
  rw [hv, eval₂_mul_of_isHomogeneous _ _ _ hp, T_pow]
  congr 2
  ring

/-- **The two Laurent evaluations agree on degree-zero fractions with denominator a power of
`x y`.** -/
theorem awayEval_laurentX_eq_laurentY (H : Away (pinchGrading I) (coordX I * coordY I)) :
    awayEval I _ (laurentX I) (isUnit_laurentX I) H =
      awayEval I _ (laurentY I) (isUnit_laurentY I) H := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (coordXY_mem I) H
  have h1 := awayEval_mk_mul I (coordXY_mem I) (laurentX I) (isUnit_laurentX I) n a ha
  have h2 := awayEval_mk_mul I (coordXY_mem I) (laurentY I) (isUnit_laurentY I) n a ha
  rw [laurentX_coordXY, T_pow] at h1
  rw [laurentY_coordXY, T_pow, laurentY_of_mem I ha, ← h1] at h2
  apply (isUnit_T ((n : ℤ) * -1)).mul_right_cancel
  rw [h2, mul_left_comm, ← T_add]
  congr 2
  simp only [smul_eq_mul]
  push_cast
  ring

theorem coeff_zero_toLaurent (p : Polynomial (R ⧸ I)) :
    (Polynomial.toLaurent p).coeff 0 = p.coeff 0 := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ 0

/-- **The algebraic heart of the example.** If two degree-zero fractions, one with denominator a
power of `x` and one with denominator a power of `y`, become equal after inverting `x y`, then
their values at `[1 : 0]` and at `[0 : 1]` are congruent modulo `I`. Modulo `I` the ring `S`
becomes `(R/I)[x, y]` and the statement is that a global function on `𝐏¹_{R/I}` is constant. -/
theorem constX_sub_constY_mem (F : Away (pinchGrading I) (coordX I))
    (G : Away (pinchGrading I) (coordY I))
    (h : awayMap _ (coordY_mem I) (rfl : coordX I * coordY I = coordX I * coordY I) F =
      awayMap _ (coordX_mem I) (mul_comm (coordX I) (coordY I)) G) :
    constX I F - constY I G ∈ I := by
  rw [← Ideal.Quotient.eq]
  have hp : Ideal.Quotient.mk I (constX I F) =
      (awayEval I _ (polyX I) (isUnit_polyX I) F).coeff 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom]
    have e1 := congrArg (fun φ => φ F) (comp_awayEval I (Ideal.Quotient.mk I) _ (evalX I)
      (isUnit_evalX I))
    have e2 := congrArg (fun φ => φ F) (comp_awayEval I (Polynomial.evalRingHom 0) _ (polyX I)
      (isUnit_polyX I))
    simp only [RingHom.comp_apply] at e1 e2
    rw [e1, e2, awayEval_congr I _ (evalZero_comp_polyX I)]
  have hq : Ideal.Quotient.mk I (constY I G) =
      (awayEval I _ (polyY I) (isUnit_polyY I) G).coeff 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom]
    have e1 := congrArg (fun φ => φ G) (comp_awayEval I (Ideal.Quotient.mk I) _ (evalY I)
      (isUnit_evalY I))
    have e2 := congrArg (fun φ => φ G) (comp_awayEval I (Polynomial.evalRingHom 0) _ (polyY I)
      (isUnit_polyY I))
    simp only [RingHom.comp_apply] at e1 e2
    rw [e1, e2, awayEval_congr I _ (evalZero_comp_polyY I)]
  have hpL : Polynomial.toLaurent (awayEval I _ (polyX I) (isUnit_polyX I) F) =
      awayEval I _ (laurentX I) (isUnit_laurentX I)
        (awayMap _ (coordY_mem I) (rfl : coordX I * coordY I = coordX I * coordY I) F) := by
    rw [← RingHom.comp_apply _ (awayMap _ _ _), awayEval_awayMap I (coordY_mem I) rfl _ _
      (isUnit_laurentX_coordX I)]
    have e := congrArg (fun φ => φ F) (comp_awayEval I Polynomial.toLaurent _ (polyX I)
      (isUnit_polyX I))
    simp only [RingHom.comp_apply] at e
    rw [e, awayEval_congr I _ (toLaurent_comp_polyX I)]
  have hqL : invert (Polynomial.toLaurent (awayEval I _ (polyY I) (isUnit_polyY I) G)) =
      awayEval I _ (laurentY I) (isUnit_laurentY I)
        (awayMap _ (coordX_mem I) (mul_comm (coordX I) (coordY I)) G) := by
    rw [← RingHom.comp_apply _ (awayMap _ _ _), awayEval_awayMap I (coordX_mem I) _ _ _
      (isUnit_laurentY_coordY I)]
    have e := congrArg (fun φ => φ G) (comp_awayEval I ((invertHom I).comp Polynomial.toLaurent)
      (coordY I) (polyY I) (isUnit_polyY I))
    simp only [RingHom.comp_apply, invertHom_apply] at e
    rw [e, awayEval_congr I _ ((RingHom.comp_assoc _ _ _).trans
      (invert_comp_toLaurent_comp_polyY I))]
  have key : Polynomial.toLaurent (awayEval I _ (polyX I) (isUnit_polyX I) F) =
      invert (Polynomial.toLaurent (awayEval I _ (polyY I) (isUnit_polyY I) G)) := by
    rw [hpL, hqL, h, awayEval_laurentX_eq_laurentY]
  have := congrArg (fun f : (R ⧸ I)[T;T⁻¹] => f.coeff 0) key
  simp only [invert_apply, neg_zero, coeff_zero_toLaurent] at this
  rw [hp, hq, this]

end Laurent

/-! ### The projective scheme `X = Proj S` and its global sections -/

/-- The projective scheme `X = Proj(R[x, y] / x y I)`. -/
abbrev pinchScheme : Scheme.{u} := AlgebraicGeometry.Proj (pinchGrading I)

/-- The structure morphism `X ⟶ Spec R`, through the degree-zero part `S₀` of `S`. -/
def pinchToSpec : pinchScheme I ⟶ Spec (.of R) :=
  AlgebraicGeometry.Proj.toSpecZero (pinchGrading I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (pinchGrading I 0)))

/-- The ring homomorphism `R → Γ(X, 𝒪_X)` making `H⁰(X, 𝒪_X)` an `R`-module. -/
def structureHom : CommRingCat.of R ⟶ Γ(pinchScheme I, ⊤) :=
  (Scheme.ΓSpecIso (.of R)).inv ≫ (pinchToSpec I).appTop

/-- Pulling a global function back to the standard chart `Spec S_(f) ⟶ X`. -/
def chartSection {f : PinchRing I} {d : ℕ} (hf : f ∈ pinchGrading I d) (hd : 0 < d) :
    Γ(pinchScheme I, ⊤) ⟶ CommRingCat.of (Away (pinchGrading I) f) :=
  (AlgebraicGeometry.Proj.awayι (pinchGrading I) f hf hd).appTop ≫ (Scheme.ΓSpecIso _).hom

theorem chartSection_comp_awayMap {f g x : PinchRing I} {d e : ℕ} (hf : f ∈ pinchGrading I d)
    (hd : 0 < d) (hg : g ∈ pinchGrading I e) (hx : x = f * g) :
    chartSection I hf hd ≫ CommRingCat.ofHom (awayMap _ hg hx) =
      chartSection I (hx ▸ SetLike.mul_mem_graded hf hg) (hd.trans_le (d.le_add_right e)) := by
  rw [chartSection, chartSection, ← AlgebraicGeometry.Proj.SpecMap_awayMap_awayι
    (𝒜 := pinchGrading I) (f_deg := hf) (hm := hd) (g_deg := hg) (hx := hx),
    Scheme.Hom.comp_appTop, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality]

theorem awayι_comp_pinchToSpec {f : PinchRing I} {d : ℕ} (hf : f ∈ pinchGrading I d)
    (hd : 0 < d) :
    AlgebraicGeometry.Proj.awayι _ f hf hd ≫ pinchToSpec I =
      Spec.map (CommRingCat.ofHom
        ((fromZeroRingHom _ _).comp (algebraMap R (pinchGrading I 0)))) := by
  rw [pinchToSpec, AlgebraicGeometry.Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

theorem chartSection_structureHom {f : PinchRing I} {d : ℕ} (hf : f ∈ pinchGrading I d)
    (hd : 0 < d) (r : R) :
    (chartSection I hf hd).hom ((structureHom I).hom r) =
      fromZeroRingHom _ _ (algebraMap R (pinchGrading I 0) r) := by
  have h := congrArg (fun φ => ((Scheme.ΓSpecIso (.of R)).inv ≫ φ.appTop ≫
    (Scheme.ΓSpecIso _).hom).hom r) (awayι_comp_pinchToSpec I hf hd)
  simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc] at h
  simpa [chartSection, structureHom] using h

theorem algebraMap_pinchRing (r : R) :
    algebraMap R (PinchRing I) r = Ideal.Quotient.mk _ (C r) := by
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]

theorem evalX_algebraMap (r : R) :
    evalX I ((algebraMap R (pinchGrading I 0) r : pinchGrading I 0) : PinchRing I) = r := by
  rw [SetLike.GradeZero.coe_algebraMap, algebraMap_pinchRing, evalX, pinchLift_mk, eval₂_C,
    RingHom.id_apply]

theorem evalY_algebraMap (r : R) :
    evalY I ((algebraMap R (pinchGrading I 0) r : pinchGrading I 0) : PinchRing I) = r := by
  rw [SetLike.GradeZero.coe_algebraMap, algebraMap_pinchRing, evalY, pinchLift_mk, eval₂_C,
    RingHom.id_apply]

/-- **The `R`-linear map `H⁰(X, 𝒪_X) → R`, `(F, G) ↦ F(0) - G(0)`**: the difference of the values
of a global function at the two points `[1 : 0]` and `[0 : 1]`, read on the two charts. -/
def constantTermDifference : Γ(pinchScheme I, ⊤) →+ R :=
  ((constX I).comp (chartSection I (coordX_mem I) one_pos).hom).toAddMonoidHom -
    ((constY I).comp (chartSection I (coordY_mem I) one_pos).hom).toAddMonoidHom

theorem constantTermDifference_apply (s : Γ(pinchScheme I, ⊤)) :
    constantTermDifference I s =
      constX I ((chartSection I (coordX_mem I) one_pos).hom s) -
        constY I ((chartSection I (coordY_mem I) one_pos).hom s) := rfl

theorem constantTermDifference_structureHom_mul (r : R) (s : Γ(pinchScheme I, ⊤)) :
    constantTermDifference I ((structureHom I).hom r * s) =
      r * constantTermDifference I s := by
  simp only [constantTermDifference_apply, map_mul]
  rw [chartSection_structureHom, chartSection_structureHom, constX, constY,
    awayEval_fromZeroRingHom, awayEval_fromZeroRingHom, evalX_algebraMap, evalY_algebraMap,
    mul_sub]

/-- The values of a global function at `[1 : 0]` and `[0 : 1]` are congruent modulo `I`. -/
theorem constantTermDifference_mem (s : Γ(pinchScheme I, ⊤)) :
    constantTermDifference I s ∈ I := by
  apply constX_sub_constY_mem
  have h1 := congrArg (fun φ => φ.hom s) (chartSection_comp_awayMap I (coordX_mem I) one_pos
    (coordY_mem I) (rfl : coordX I * coordY I = coordX I * coordY I))
  have h2 := congrArg (fun φ => φ.hom s) (chartSection_comp_awayMap I (coordY_mem I) one_pos
    (coordX_mem I) (mul_comm (coordX I) (coordY I)))
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h1 h2
  rw [h1, h2]

/-- The pullback along an open immersion `j` of a global section only depends on its restriction
to an open containing the image of `j`. -/
theorem appTop_eq_appLE {Y Z : Scheme.{u}} (j : Y ⟶ Z) (U : Z.Opens) (hU : ⊤ ≤ j ⁻¹ᵁ U)
    (s : Γ(Z, ⊤)) :
    j.appTop s = j.appLE U ⊤ hU (Z.presheaf.map (homOfLE le_top).op s) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl

/-- A global section whose pullback along an open immersion `j` vanishes restricts to zero on the
image of `j`. -/
theorem restrict_image_top_eq_zero {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    {s : Γ(Z, ⊤)} (h : j.appTop s = 0) :
    Z.presheaf.map (homOfLE (le_top : j ''ᵁ ⊤ ≤ ⊤)).op s = 0 := by
  have key := Scheme.Hom.appLE_appIso_inv_apply j (U := ⊤) (V := ⊤) le_top s
  have e : j.appLE ⊤ ⊤ le_top = j.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [e, h, map_zero] at key
  exact key.symm

theorem top_le_preimage_basicOpen {f : PinchRing I} {d : ℕ} (hf : f ∈ pinchGrading I d)
    (hd : 0 < d) :
    ⊤ ≤ AlgebraicGeometry.Proj.awayι _ f hf hd ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (pinchGrading I) f := by
  intro p _
  change (AlgebraicGeometry.Proj.awayι _ f hf hd).base p ∈
    AlgebraicGeometry.Proj.basicOpen (pinchGrading I) f
  rw [← AlgebraicGeometry.Proj.opensRange_awayι _ f hf hd]
  exact ⟨p, rfl⟩

theorem chartSection_eq_of_restrict_eq {f : PinchRing I} {d : ℕ} (hf : f ∈ pinchGrading I d)
    (hd : 0 < d) {s t : Γ(pinchScheme I, ⊤)}
    (h : (pinchScheme I).presheaf.map
        (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen (pinchGrading I) f ≤ ⊤)).op s =
      (pinchScheme I).presheaf.map (homOfLE le_top).op t) :
    (chartSection I hf hd).hom s = (chartSection I hf hd).hom t := by
  simp only [chartSection, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [appTop_eq_appLE _ _ (top_le_preimage_basicOpen I hf hd) s,
    appTop_eq_appLE _ _ (top_le_preimage_basicOpen I hf hd) t, h]

theorem chartSection_eq_zero_of_restrict_eq_zero {f : PinchRing I} {d : ℕ}
    (hf : f ∈ pinchGrading I d) (hd : 0 < d) {s : Γ(pinchScheme I, ⊤)}
    (h : (pinchScheme I).presheaf.map
        (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen (pinchGrading I) f ≤ ⊤)).op s = 0) :
    (chartSection I hf hd).hom s = 0 := by
  have h0 := chartSection_eq_of_restrict_eq I hf hd (s := s) (t := 0) (by rw [h, map_zero])
  rwa [map_zero] at h0

/-- A global function whose pullback to the chart `Spec S_(f)` vanishes restricts to zero on
`D₊(f)`. -/
theorem restrict_eq_zero_of_chartSection_eq_zero {f : PinchRing I} {d : ℕ}
    (hf : f ∈ pinchGrading I d) (hd : 0 < d) {s : Γ(pinchScheme I, ⊤)}
    (h : (chartSection I hf hd).hom s = 0) :
    (pinchScheme I).presheaf.map
      (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen (pinchGrading I) f ≤ ⊤)).op s = 0 := by
  have happ : (AlgebraicGeometry.Proj.awayι (pinchGrading I) f hf hd).appTop s = 0 := by
    have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Away (pinchGrading I) f))).inv.hom h
    rw [map_zero] at h'
    rw [← h']
    simp only [chartSection, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (Iso.hom_inv_id_apply _ _).symm
  have key := restrict_image_top_eq_zero _ happ
  have hW : AlgebraicGeometry.Proj.basicOpen (pinchGrading I) f ≤
      (AlgebraicGeometry.Proj.awayι (pinchGrading I) f hf hd) ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, AlgebraicGeometry.Proj.opensRange_awayι]
  have := congrArg ((pinchScheme I).presheaf.map (homOfLE hW).op) key
  rw [map_zero, ← CommRingCat.comp_apply, ← Functor.map_comp] at this
  exact this

theorem basicOpen_sup_basicOpen :
    ⊤ ≤ AlgebraicGeometry.Proj.basicOpen (pinchGrading I) (coordX I) ⊔
      AlgebraicGeometry.Proj.basicOpen (pinchGrading I) (coordY I) := by
  have hadj : Algebra.adjoin (pinchGrading I 0) (Set.range ![coordX I, coordY I]) = ⊤ := by
    have key : ∀ p : MvPolynomial (Fin 2) R, Ideal.Quotient.mk (pinchIdeal I).toIdeal p ∈
        Algebra.adjoin (pinchGrading I 0) (Set.range ![coordX I, coordY I]) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r =>
        have hr : Ideal.Quotient.mk (pinchIdeal I).toIdeal (C r) ∈ pinchGrading I 0 :=
          RingTheory.HomogeneousQuotient.quotientGrading_mk_mem _ _ (by
            rw [mem_homogeneousSubmodule]; exact isHomogeneous_C _ r)
        exact Subalgebra.algebraMap_mem _ (⟨_, hr⟩ : pinchGrading I 0)
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul]
        refine mul_mem hp (Algebra.subset_adjoin ⟨i, ?_⟩)
        fin_cases i <;> rfl
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact key p
  rw [← AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' (pinchGrading I) ![coordX I, coordY I]
    (fun i => ⟨1, by fin_cases i; exacts [coordX_mem I, coordY_mem I]⟩) hadj]
  refine iSup_le fun i => ?_
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- **Every element of `I` is attained.** For `a ∈ I` the function equal to `a` on `D₊(x)` and to
`0` on `D₊(y)` glues, because `a x y = 0` makes `a` vanish on `D₊(x y)`. -/
theorem exists_constantTermDifference_eq {a : R} (ha : a ∈ I) :
    ∃ s : Γ(pinchScheme I, ⊤), constantTermDifference I s = a := by
  set U := AlgebraicGeometry.Proj.basicOpen (pinchGrading I) (coordX I)
  set V := AlgebraicGeometry.Proj.basicOpen (pinchGrading I) (coordY I)
  set t : Γ(pinchScheme I, ⊤) := (structureHom I).hom a
  have hxy0 : (chartSection I (coordXY_mem I) two_pos).hom t = 0 := by
    rw [chartSection_structureHom]
    apply val_injective
    rw [val_zero]
    change algebraMap (PinchRing I) (Localization.Away (coordX I * coordY I))
      ((algebraMap R (pinchGrading I 0) a : pinchGrading I 0) : PinchRing I) = 0
    rw [SetLike.GradeZero.coe_algebraMap, IsLocalization.map_eq_zero_iff
      (Submonoid.powers (coordX I * coordY I))]
    refine ⟨⟨coordX I * coordY I, Submonoid.mem_powers _⟩, ?_⟩
    change coordX I * coordY I * algebraMap R (PinchRing I) a = 0
    rw [algebraMap_pinchRing]
    exact coordX_mul_coordY_mul_C I ha
  have hUV : U ⊓ V = AlgebraicGeometry.Proj.basicOpen (pinchGrading I) (coordX I * coordY I) :=
    (AlgebraicGeometry.Proj.basicOpen_mul _ _ _).symm
  have hzero : (pinchScheme I).presheaf.map (homOfLE (le_top : U ⊓ V ≤ ⊤)).op t = 0 := by
    have h := restrict_eq_zero_of_chartSection_eq_zero I (coordXY_mem I) two_pos hxy0
    have := congrArg ((pinchScheme I).presheaf.map (homOfLE hUV.le).op) h
    rw [map_zero, ← CommRingCat.comp_apply, ← Functor.map_comp] at this
    exact this
  let sUV := ((pinchScheme I).sheaf.objSupIsoProdEqLocus U V).inv.hom
    ⟨((pinchScheme I).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t, 0), by
      change (pinchScheme I).presheaf.map (homOfLE inf_le_left).op
          ((pinchScheme I).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) =
        (pinchScheme I).presheaf.map (homOfLE inf_le_right).op 0
      rw [map_zero, ← CommRingCat.comp_apply, ← Functor.map_comp]
      exact hzero⟩
  let s := (pinchScheme I).presheaf.map (homOfLE (basicOpen_sup_basicOpen I)).op sUV
  have hsU : (pinchScheme I).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
      (pinchScheme I).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t := by
    have h := TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst (pinchScheme I).sheaf U V
      ⟨((pinchScheme I).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t, 0), by
        change (pinchScheme I).presheaf.map (homOfLE inf_le_left).op
            ((pinchScheme I).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) =
          (pinchScheme I).presheaf.map (homOfLE inf_le_right).op 0
        rw [map_zero, ← CommRingCat.comp_apply, ← Functor.map_comp]
        exact hzero⟩
    simp only [s]
    exact h
  have hsV : (pinchScheme I).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s = 0 := by
    have h := TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd (pinchScheme I).sheaf U V
      ⟨((pinchScheme I).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t, 0), by
        change (pinchScheme I).presheaf.map (homOfLE inf_le_left).op
            ((pinchScheme I).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) =
          (pinchScheme I).presheaf.map (homOfLE inf_le_right).op 0
        rw [map_zero, ← CommRingCat.comp_apply, ← Functor.map_comp]
        exact hzero⟩
    simp only [s]
    exact h
  refine ⟨s, ?_⟩
  rw [constantTermDifference_apply, chartSection_eq_of_restrict_eq I _ _ hsU,
    chartSection_eq_zero_of_restrict_eq_zero I _ _ hsV, map_zero, sub_zero,
    chartSection_structureHom]
  simp only [constX, awayEval_fromZeroRingHom, evalX_algebraMap]

/-! ### `X` is a closed subscheme of `𝐏¹_R` -/

/-- The surjection `R[x, y] → S` as a homomorphism of graded rings. -/
abbrev pinchQuotient :
    homogeneousSubmodule (Fin 2) R →+*ᵍ pinchGrading I :=
  RingTheory.HomogeneousQuotient.quotientMk (homogeneousSubmodule (Fin 2) R) (pinchIdeal I)

theorem eventually_surjective_pinchQuotient :
    ∀ᶠ d : ℕ in Filter.atTop, Function.Surjective ((pinchQuotient I).gradedAddHom d) :=
  Filter.Eventually.of_forall
    (RingTheory.HomogeneousQuotient.surjective_gradedAddHom_quotientMk _ _)

theorem mapDomain_pinchQuotient :
    Stacks.AlgebraicGeometry.ProjShared.mapDomain _ _ (pinchQuotient I) = ⊤ :=
  Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective _ _ _
    (eventually_surjective_pinchQuotient I)

/-- **The closed immersion `X ⟶ 𝐏¹_R`** induced by the surjection `R[x, y] → S`. -/
def pinchToProjectiveLine :
    pinchScheme I ⟶ _root_.AlgebraicGeometry.projectiveSpaceOver 1 (Spec (.of R)) :=
  Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop _ _ (pinchQuotient I)
      (mapDomain_pinchQuotient I) ≫
    (Stacks.ProjectiveCohomology.projModelIso R 1).hom

instance isClosedImmersion_pinchToProjectiveLine :
    IsClosedImmersion (pinchToProjectiveLine I) := by
  have := Stacks.AlgebraicGeometry.SegreClosedImmersion.isClosedImmersion_mapHomOfTop _ _
    (pinchQuotient I) (mapDomain_pinchQuotient I) (eventually_surjective_pinchQuotient I)
  rw [pinchToProjectiveLine]
  infer_instance

theorem pinchToProjectiveLine_comp :
    pinchToProjectiveLine I ≫
        (_root_.AlgebraicGeometry.projectiveSpaceOver 1 (Spec (.of R)) ↘ Spec (.of R)) =
      pinchToSpec I := by
  change pinchToProjectiveLine I ≫ Limits.pullback.fst _ _ = _
  rw [pinchToProjectiveLine, Category.assoc,
    Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism,
    Stacks.ProjectiveCohomology.projModelToSpec_eq,
    Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_toSpecZero_assoc, pinchToSpec,
    ← Spec.map_comp]
  congr 2
  ext r
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [Stacks.AlgebraicGeometry.RelativeProj.coe_zeroHom_apply, SetLike.GradeZero.coe_algebraMap,
    algebraMap_pinchRing]
  rfl

/-- `X ⟶ Spec R` is H-projective: a closed subscheme of `𝐏¹_R` over `R`. -/
theorem isProjectiveMorphism_pinchToSpec : IsProjectiveMorphism (pinchToSpec I) :=
  ⟨1, pinchToProjectiveLine I, inferInstance, pinchToProjectiveLine_comp I⟩

/-- `X ⟶ Spec R` is projective in the sense of Stacks Tag 01W8. -/
theorem isProjective_pinchToSpec : IsProjective (pinchToSpec I) :=
  (isProjective_iff_isProjectiveMorphism_of_isAffine _).mpr (isProjectiveMorphism_pinchToSpec I)

/-! ### The pushforward `i_* 𝒪_X`, a finite type quasi-coherent module on `𝐏¹_R` -/

/-- The structure homomorphism `R → Γ(𝐏¹_R, 𝒪)`. -/
def projectiveLineStructureHom :
    CommRingCat.of R ⟶ Γ(projectiveSpaceOverRing 1 (.of R), ⊤) :=
  (Scheme.ΓSpecIso (.of R)).inv ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)).appTop

theorem structureHom_eq :
    structureHom I = projectiveLineStructureHom ≫ (pinchToProjectiveLine I).appTop := by
  rw [structureHom, projectiveLineStructureHom, ← pinchToProjectiveLine_comp I,
    Scheme.Hom.comp_appTop, Category.assoc]

/-- The module `i_* 𝒪_X` on `𝐏¹_R`, for the closed immersion `i : X ⟶ 𝐏¹_R`. -/
def pinchSheaf : (projectiveSpaceOverRing 1 (.of R)).Modules :=
  (Scheme.Modules.pushforward (pinchToProjectiveLine I)).obj
    (SheafOfModules.unit (pinchScheme I).ringCatSheaf)

instance isQuasicoherent_pinchSheaf : (pinchSheaf I).IsQuasicoherent := by
  unfold pinchSheaf
  infer_instance

instance isFiniteType_pinchSheaf : (pinchSheaf I).IsFiniteType :=
  Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isFinite _ _

/-- A linear map from a finite module onto an ideal makes the ideal finitely generated. -/
theorem fg_of_range_eq {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (Φ : M →ₗ[R] R) (h : LinearMap.range Φ = I) : I.FG := by
  have := (Module.Finite.fg_top (R := R) (M := M)).map Φ
  rwa [← LinearMap.range_eq_map, h] at this

theorem range_eq_of_constantTermDifference {M : Type*} [AddCommGroup M] [Module R M]
    (Φ : M →ₗ[R] R) (e : M → Γ(pinchScheme I, ⊤)) (e' : Γ(pinchScheme I, ⊤) → M)
    (hΦ : ∀ m, Φ m = constantTermDifference I (e m))
    (he : ∀ s, e (e' s) = s) : LinearMap.range Φ = I := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [hΦ]
    exact constantTermDifference_mem I _
  · intro a ha
    obtain ⟨s, hs⟩ := exists_constantTermDifference_eq I ha
    exact ⟨e' s, by rw [hΦ, he, hs]⟩

/-- **`H⁰(𝐏¹_R, i_* 𝒪_X)` is not a finite `R`-module** when `I` is not finitely generated. -/
theorem not_finite_pinchSheaf (hI : ¬ I.FG) :
    ¬ Module.Finite R ((ModuleCat.restrictScalars (projectiveLineStructureHom (R := R)).hom).obj
      ((pinchSheaf I).val.obj (Opposite.op ⊤))) := by
  intro hfin
  let Φ : (ModuleCat.restrictScalars (projectiveLineStructureHom (R := R)).hom).obj
      ((pinchSheaf I).val.obj (Opposite.op ⊤)) →ₗ[R] R :=
    { toFun := fun m => constantTermDifference I m
      map_add' := fun m m' => map_add (constantTermDifference I) m m'
      map_smul' := fun r m => by
        change constantTermDifference I
            ((pinchToProjectiveLine I).appTop.hom (projectiveLineStructureHom.hom r) *
              (show Γ(pinchScheme I, ⊤) from m)) =
          r * constantTermDifference I m
        rw [← CommRingCat.comp_apply, ← structureHom_eq,
          constantTermDifference_structureHom_mul] }
  exact hI (fg_of_range_eq I Φ (range_eq_of_constantTermDifference I Φ (fun m => m)
    (fun s => s) (fun _ => rfl) (fun _ => rfl)))

/-- **`H⁰(X, 𝒪_X)` is not a finite `R`-module** when `I` is not finitely generated. -/
theorem not_finite_structureHom (hI : ¬ I.FG) : ¬ (structureHom I).hom.Finite := by
  intro hfin
  let := (structureHom I).hom.toAlgebra
  have : Module.Finite R Γ(pinchScheme I, ⊤) := hfin
  let Φ : Γ(pinchScheme I, ⊤) →ₗ[R] R :=
    { toFun := constantTermDifference I
      map_add' := map_add _
      map_smul' := fun r s => by
        change constantTermDifference I ((structureHom I).hom r * s) =
          r * constantTermDifference I s
        rw [constantTermDifference_structureHom_mul] }
  exact hI (fg_of_range_eq I Φ (range_eq_of_constantTermDifference I Φ id id
    (fun _ => rfl) (fun _ => rfl)))

end Stacks.Examples.NonfiniteGlobalSections

namespace Stacks.Examples

open NonfiniteGlobalSections

/-- **Stacks Project, Tag 0HAT (Non-finite `H⁰`).**
1. There exist a ring `R` and a projective scheme `X` over `R` such that `H⁰(X, 𝒪_X)` is not a
   finite `R`-module. Here `f : X ⟶ Spec R` is projective both in the sense of Tag 01W8
   (`AlgebraicGeometry.IsProjective`) and in the H-projective sense
   (`AlgebraicGeometry.IsProjectiveMorphism`, a closed immersion into `𝐏ⁿ_R` over `R`), and
   `H⁰(X, 𝒪_X) = Γ(X, 𝒪_X)` is an `R`-module through `R ≅ Γ(Spec R, 𝒪) → Γ(X, 𝒪_X)`.
2. There exist a ring `R` and a quasi-coherent module `𝓕` of finite type on `𝐏¹_R` such that
   `H⁰(𝐏¹_R, 𝓕)` is not a finite `R`-module, `H⁰(𝐏¹_R, 𝓕) = Γ(𝐏¹_R, 𝓕)` being an `R`-module
   through the structure morphism `𝐏¹_R ⟶ Spec R`.

Following the source, `R` is a ring with an ideal `I` that is not finitely generated, `X` is
`Proj(R[x, y] / x y I)` (`Stacks.Examples.NonfiniteGlobalSections.pinchScheme`) and `𝓕 = i_* 𝒪_X`
for the closed immersion `i : X ⟶ 𝐏¹_R` (`Stacks.Examples.NonfiniteGlobalSections.pinchSheaf`);
the ring is `k[x₀, x₁, …]/(x₀², x₁², …)` over `k = ℚ`, whose ideal `(x₀, x₁, …)` is not finitely
generated (`Stacks.Examples.infiniteSquareZeroVariableIdeal_not_fg`). The ring and both schemes
live in an arbitrary universe. -/
@[stacks 0HAT]
theorem exists_projective_not_finite_globalSections :
    (∃ (R : Type u) (_ : CommRing R) (X : Scheme.{u}) (f : X ⟶ Spec (.of R)),
      IsProjective f ∧ IsProjectiveMorphism f ∧
        ¬ ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.Finite) ∧
    (∃ (R : Type u) (_ : CommRing R) (F : (projectiveSpaceOverRing 1 (.of R)).Modules),
      F.IsQuasicoherent ∧ F.IsFiniteType ∧
        ¬ Module.Finite R ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of R)).inv ≫
          (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)).appTop).hom).obj
            (F.val.obj (Opposite.op ⊤)))) := by
  have hI := infiniteSquareZeroVariableIdeal_not_fg (ULift.{u} ℚ)
  exact ⟨⟨_, inferInstance, pinchScheme _, pinchToSpec _, isProjective_pinchToSpec _,
      isProjectiveMorphism_pinchToSpec _, not_finite_structureHom _ hI⟩,
    ⟨_, inferInstance, pinchSheaf _, inferInstance, inferInstance, not_finite_pinchSheaf _ hI⟩⟩

end Stacks.Examples

end
