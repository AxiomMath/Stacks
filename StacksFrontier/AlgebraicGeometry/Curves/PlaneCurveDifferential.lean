module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.Defs

/-!
# Plane curves and their distinguished differential (Stacks 09U0)

An irreducible polynomial `f` in two variables over a field cuts out an integral affine
plane curve; its coordinate ring is `k[x, y]/(f)` and its function field `K` is the fraction
field of that ring. Writing `f_x` and `f_y` for the images in `K` of the two partial
derivatives of `f`, at least one of them is nonzero, and the element

  `ω = dx/f_y = -dy/f_x`

of `Ω[K⁄k]` is well defined and nonzero. This is the differential of the final-exam
situation Stacks 09U0, where `f` is the dehomogenization `F(1, x, y)` of an irreducible
homogeneous `F` in three variables and the plane curve is the projective curve `D = V(F)`.

## Main definitions

* `AlgebraicGeometry.AffinePlaneCurve`: an irreducible affine plane curve over a field,
  given by its equation.
* `AlgebraicGeometry.AffinePlaneCurve.coordinateRing`,
  `AlgebraicGeometry.AffinePlaneCurve.FunctionField`: its coordinate ring and function field.
* `AlgebraicGeometry.AffinePlaneCurve.x`, `AlgebraicGeometry.AffinePlaneCurve.y`,
  `AlgebraicGeometry.AffinePlaneCurve.partialX`,
  `AlgebraicGeometry.AffinePlaneCurve.partialY`: the two coordinates and the two partial
  derivatives of the equation, read in the function field.
* `AlgebraicGeometry.AffinePlaneCurve.differential`: **Stacks 09U0**, the differential `ω`.
* `AlgebraicGeometry.ProjectivePlaneCurve`: an irreducible projective plane curve `D = V(F)`
  together with the affine plane curve its standard chart cuts out, and
  `AlgebraicGeometry.ProjectivePlaneCurve.curve`,
  `AlgebraicGeometry.ProjectivePlaneCurve.inclusion`: the reduced projective curve and its
  closed immersion into the projective plane.

## Main results

* `AlgebraicGeometry.AffinePlaneCurve.isCurve_structureMap`: the affine plane curve of an
  irreducible equation is a curve over the base field in the sense of Stacks 0A23.
* `AlgebraicGeometry.AffinePlaneCurve.partialX_ne_zero_or_partialY_ne_zero`: **Stacks
  09U0**, at least one partial derivative is nonzero in the function field. This needs the
  base field to be perfect.
* `AlgebraicGeometry.AffinePlaneCurve.inv_partialY_smul_D_x_eq_neg_inv_partialX_smul_D_y`:
  **Stacks 09U0**, the two formulas for `ω` agree where both are defined.
* `AlgebraicGeometry.AffinePlaneCurve.inv_partialY_smul_D_x_ne_zero` and
  `AlgebraicGeometry.AffinePlaneCurve.neg_inv_partialX_smul_D_y_ne_zero`: **Stacks 09U0**,
  each formula is nonzero where it is defined.
* `AlgebraicGeometry.AffinePlaneCurve.differential_eq_inv_partialY_smul_D_x`,
  `AlgebraicGeometry.AffinePlaneCurve.differential_eq_neg_inv_partialX_smul_D_y` and
  `AlgebraicGeometry.AffinePlaneCurve.differential_ne_zero`: `ω` is given by either formula
  wherever that formula is defined, and is nonzero.

## Implementation notes

The ideal `(f)` is prime because `k[x, y]` is a unique factorization domain, and that is
registered as an instance, so that `Ideal.Quotient.isDomain` makes the coordinate ring a
domain and its fraction field a field without any further argument. The curve is therefore
presented by a structure carrying the equation and its irreducibility, rather than by loose
hypotheses: the instance cannot be derived from a `Prop` argument that is not in scope.

Division of a differential by a nonzero element of the function field is written as scalar
multiplication by the inverse. The chosen branch of the formula for `ω` is the one with
`f_y` in the denominator whenever `f_y ≠ 0`, which is a decision taken with
`Classical.propDecidable`; `differential_eq_inv_partialY_smul_D_x` and
`differential_eq_neg_inv_partialX_smul_D_y` show that either branch may be used wherever its
denominator is nonzero, so no consumer need know which was chosen.

That at least one partial derivative of an irreducible `f` is nonzero as a *polynomial* uses
perfectness of `k`: in characteristic `p` a polynomial killed by both partial derivatives is
a `p`-th power of a polynomial whose coefficients are the `p`-th roots of its own, hence is
not irreducible. This is the only place where anything beyond `Field k` is used, so the
hypothesis is `PerfectField k` and not algebraic closedness, which is what the source
assumes. That the nonzero partial derivative survives in the function field is a degree
count: `f` cannot divide a nonzero polynomial of smaller total degree.

That `dx` and `dy` are nonzero in `Ω[K⁄k]` when the corresponding partial derivative is
nonzero is proved by exhibiting a `K`-linear functional on `Ω[K⁄k]` taking `dx` to `f_y` and
`dy` to `-f_x`. It is built from the derivation `f_y ∂/∂x - f_x ∂/∂y` of `k[x, y]`, which
kills `f` and therefore descends to the coordinate ring, and is then transported to the
function field: the fraction field of a domain is formally étale over it, so
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` identifies `Ω[K⁄k]` with the base
change of `Ω[A⁄k]`.

The relation `f_x · dx + f_y · dy = 0` in `Ω[K⁄k]` comes from `d f = 0`, expanded in the
basis `dX₀, dX₁` of `Ω[k[x,y]⁄k]` and pushed to `K` along
`KaehlerDifferential.mapBaseChange`.

Projective points are relevant homogeneous prime ideals of the standard graded polynomial
ring in three variables; the projective plane curve is the reduced induced closed subscheme
of the vanishing set of `F`, and its inclusion into the projective plane is the subscheme
immersion. That the dehomogenization `F(1, x, y)` of an irreducible `F` not divisible by the
first coordinate is itself irreducible is carried as a field of
`AlgebraicGeometry.ProjectivePlaneCurve` rather than proved.

## References

* [Stacks Project, Tag 09U0](https://stacks.math.columbia.edu/tag/09U0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- An *irreducible affine plane curve* over a field `k`: an irreducible polynomial in two
variables, which cuts out an integral curve in the affine plane. -/
structure AffinePlaneCurve (k : Type u) [Field k] where
  /-- The defining equation of the curve. -/
  equation : MvPolynomial (Fin 2) k
  /-- The defining equation is irreducible. -/
  irreducible_equation : Irreducible equation

namespace AffinePlaneCurve

variable {k : Type u} [Field k] (C : AffinePlaneCurve k)

/-- The ideal of the polynomial ring in two variables cut out by the equation of `C`. -/
abbrev ideal : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ({C.equation} : Set (MvPolynomial (Fin 2) k))

/-- The ideal generated by an irreducible plane equation is prime, because the polynomial
ring is a unique factorization domain. -/
instance isPrime_ideal : C.ideal.IsPrime := by
  rw [AffinePlaneCurve.ideal, Ideal.span_singleton_prime C.irreducible_equation.ne_zero]
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp C.irreducible_equation

/-- The coordinate ring of the affine plane curve `C`, namely `k[x, y]/(f)`. -/
abbrev coordinateRing := MvPolynomial (Fin 2) k ⧸ C.ideal

/-- The function field of the affine plane curve `C`, namely the fraction field of its
coordinate ring. -/
abbrev FunctionField := FractionRing C.coordinateRing

/-- The structure morphism of the affine plane curve `C` over its base field. -/
def structureMap : Spec (.of C.coordinateRing) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k C.coordinateRing))

/-- The image in the coordinate ring of a polynomial in two variables. -/
abbrev toCoordinateRing (p : MvPolynomial (Fin 2) k) : C.coordinateRing :=
  Ideal.Quotient.mk C.ideal p

/-- The image in the function field of a polynomial in two variables. -/
abbrev eval (p : MvPolynomial (Fin 2) k) : C.FunctionField :=
  algebraMap C.coordinateRing C.FunctionField (C.toCoordinateRing p)

/-- The first affine coordinate, read in the function field of `C`. -/
abbrev x : C.FunctionField := C.eval (MvPolynomial.X (0 : Fin 2))

/-- The second affine coordinate, read in the function field of `C`. -/
abbrev y : C.FunctionField := C.eval (MvPolynomial.X (1 : Fin 2))

/-- The partial derivative of the equation with respect to the first coordinate, read in the
function field of `C`. -/
abbrev partialX : C.FunctionField :=
  C.eval (MvPolynomial.pderiv (0 : Fin 2) C.equation)

/-- The partial derivative of the equation with respect to the second coordinate, read in
the function field of `C`. -/
abbrev partialY : C.FunctionField :=
  C.eval (MvPolynomial.pderiv (1 : Fin 2) C.equation)

/-! ### The affine plane curve is a curve -/

/-- The affine plane curve cut out by an irreducible equation is a curve over its base field
in the sense of Stacks 0A23: an integral separated scheme of finite type over `k` of
dimension one. -/
instance isCurve_structureMap : IsCurve k C.structureMap := by
  classical
  let R := MvPolynomial (Fin 2) k
  let I : Ideal R := C.ideal
  let A := C.coordinateRing
  let q : R →ₐ[k] A := { Ideal.Quotient.mk I with commutes' := fun _ => rfl }
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  let p : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hcomap : PrimeSpectrum.comap q.toRingHom p = ⟨I, C.isPrime_ideal⟩ :=
    PrimeSpectrum.ext Ideal.mk_ker
  have hheight : I.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr C.irreducible_equation.ne_zero)
      C.irreducible_equation.not_isUnit
  let _ : Algebra.FiniteType k A := Algebra.FiniteType.of_surjective q hq
  have hdim := PrimeSpectrum.localKrullDim_add_height_comap_eq_natCard_add_height k q hq p
  rw [hcomap, hheight, Ideal.height_bot, Nat.card_fin] at hdim
  norm_num at hdim
  have hringdim : ringKrullDim A = 1 := by
    rw [PrimeSpectrum.localKrullDim_eq_ringKrullDim_of_isDomain k A p] at hdim
    have hdim' : ringKrullDim A + 1 = (1 : WithBot ℕ∞) + 1 := by
      norm_num at hdim ⊢
      exact hdim
    exact ENat.WithBot.add_one_cancel.mp hdim'
  have htopdim : topologicalKrullDim (Spec (.of A)) = 1 := by
    change topologicalKrullDim (PrimeSpectrum A) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hringdim]
  have hfinitePoly : (algebraMap k R).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hfinite : (algebraMap k A).FiniteType := by
    convert RingHom.FiniteType.comp_surjective hfinitePoly hq using 1
  have hvariety : IsVariety k C.structureMap :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hfinite
      toQuasiCompact := inferInstance }
  exact (isCurve_iff k C.structureMap).2 ⟨hvariety, htopdim⟩

/-! ### At least one partial derivative is nonzero -/

private theorem pderiv_totalDegree_lt (f : MvPolynomial (Fin 2) k) (i : Fin 2)
    (h : MvPolynomial.pderiv i f ≠ 0) :
    (MvPolynomial.pderiv i f).totalDegree < f.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  have hpos : 0 < f.totalDegree := by
    by_contra hnot
    have hz : f.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hz
    rw [hz, MvPolynomial.pderiv_C] at h
    exact h rfl
  apply (Finset.sup_lt_iff hpos).mpr
  intro m hm
  have hc : (MvPolynomial.pderiv i f).coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hc' : f.coeff (m + Finsupp.single i 1) ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hs : m + Finsupp.single i 1 ∈ f.support := MvPolynomial.mem_support_iff.mpr hc'
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    simp [Finsupp.sum_add_index]
  have hle := MvPolynomial.le_totalDegree hs
  omega

/-- If `∂f/∂xᵢ = 0`, then the exponent of `xᵢ` in every monomial of `f` is zero in `k`. -/
private theorem natCast_exponent_eq_zero_of_pderiv_eq_zero
    (f : MvPolynomial (Fin 2) k) (i : Fin 2)
    (hderiv : MvPolynomial.pderiv i f = 0) (m : Fin 2 →₀ ℕ)
    (hm : m ∈ f.support) : (m i : k) = 0 := by
  by_cases hpos : 0 < m i
  · have hz : (MvPolynomial.pderiv i f).coeff
        (m - Finsupp.single i 1) = 0 := by simp [hderiv]
    have hidx : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
      Finsupp.sub_add_single_one_cancel (ne_of_gt hpos)
    have hcastEq : ((m i - 1 : ℕ) : k) + 1 = (m i : k) := by
      calc ((m i - 1 : ℕ) : k) + 1 = ((m i - 1 + 1 : ℕ) : k) := by norm_cast
        _ = (m i : k) := by rw [Nat.sub_add_cancel (by omega)]
    rw [MvPolynomial.coeff_pderiv, hidx, Finsupp.tsub_apply, Finsupp.single_eq_same,
      hcastEq] at hz
    exact (mul_eq_zero.mp hz).resolve_left (MvPolynomial.mem_support_iff.mp hm)
  · simp [Nat.eq_zero_of_not_pos hpos]

private theorem exponent_dvd_of_pderiv_eq_zero {p : ℕ} [Fact p.Prime] [CharP k p]
    (f : MvPolynomial (Fin 2) k) (i : Fin 2)
    (hderiv : MvPolynomial.pderiv i f = 0) (m : Fin 2 →₀ ℕ)
    (hm : m ∈ f.support) : p ∣ m i :=
  (CharP.cast_eq_zero_iff k p (m i)).mp
    (natCast_exponent_eq_zero_of_pderiv_eq_zero f i hderiv m hm)

private theorem exponent_eq_zero_of_pderiv_eq_zero [CharZero k]
    (f : MvPolynomial (Fin 2) k) (i : Fin 2)
    (hderiv : MvPolynomial.pderiv i f = 0) (m : Fin 2 →₀ ℕ)
    (hm : m ∈ f.support) : m i = 0 :=
  Nat.cast_eq_zero.mp (natCast_exponent_eq_zero_of_pderiv_eq_zero f i hderiv m hm)

/-- The exponent vector `m` divided by `p`, used to extract a `p`-th root of a polynomial
all of whose exponents are divisible by `p`. -/
private def divideExponent (p : ℕ) (m : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (m 0 / p) + Finsupp.single 1 (m 1 / p)

private theorem smul_divideExponent {p : ℕ} (m : Fin 2 →₀ ℕ)
    (hm : ∀ i : Fin 2, p ∣ m i) : p • divideExponent p m = m := by
  ext i
  fin_cases i <;> simp [divideExponent, Nat.mul_div_cancel' (hm 0), Nat.mul_div_cancel' (hm 1)]

/-- The two partial derivatives of an irreducible polynomial in two variables over a perfect
field are not both zero. -/
private theorem pderivs_not_both_zero [PerfectField k] {f : MvPolynomial (Fin 2) k}
    (hf : Irreducible f) :
    MvPolynomial.pderiv 0 f ≠ 0 ∨ MvPolynomial.pderiv 1 f ≠ 0 := by
  classical
  by_contra! hboth
  obtain ⟨hdx, hdy⟩ := hboth
  rcases CharP.exists' k with hchar | ⟨p, hp, hchar⟩
  · let _ : CharZero k := hchar
    have hconstant (m : Fin 2 →₀ ℕ) (hm : m ∈ f.support) : m = 0 := by
      ext i
      fin_cases i
      · exact exponent_eq_zero_of_pderiv_eq_zero f 0 hdx m hm
      · exact exponent_eq_zero_of_pderiv_eq_zero f 1 hdy m hm
    have hfC : f = MvPolynomial.C (f.coeff 0) := by
      ext m
      by_cases hm0 : m = 0
      · subst m
        simp
      · rw [MvPolynomial.notMem_support_iff.mp fun hm => hm0 (hconstant m hm),
          MvPolynomial.coeff_C_of_ne_zero hm0]
    have hc : f.coeff 0 ≠ 0 := fun hz => hf.ne_zero (by rw [hfC, hz, map_zero])
    exact hf.not_isUnit (by
      rw [hfC]
      exact (isUnit_iff_ne_zero.mpr hc).map (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k))
  · let _ : Fact p.Prime := hp
    let _ : CharP k p := hchar
    let _ : ExpChar k p := .prime hp.out
    have hdiv : ∀ m ∈ f.support, ∀ i : Fin 2, p ∣ m i := by
      intro m hm i
      fin_cases i
      · exact exponent_dvd_of_pderiv_eq_zero f 0 hdx m hm
      · exact exponent_dvd_of_pderiv_eq_zero f 1 hdy m hm
    let root (m : Fin 2 →₀ ℕ) := (frobeniusEquiv k p).symm (f.coeff m)
    let g : MvPolynomial (Fin 2) k :=
      ∑ m ∈ f.support, MvPolynomial.monomial (divideExponent p m) (root m)
    have hg : g ^ p = f := by
      dsimp [g]
      rw [sum_pow_char p]
      conv_rhs => rw [MvPolynomial.as_sum f]
      apply Finset.sum_congr rfl
      intro m hm
      rw [MvPolynomial.monomial_pow, smul_divideExponent (p := p) m (hdiv m hm)]
      simp [root, frobeniusEquiv_symm_pow_p]
    have hfac : f = g * g ^ (p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hp.out.pos, hg]
    have hunitg : IsUnit g := (hf.isUnit_or_isUnit hfac).elim id fun h =>
      isUnit_of_dvd_unit (dvd_pow_self g (by have := hp.out.two_le; omega)) h
    exact hf.not_isUnit (hg ▸ hunitg.pow p)

private theorem eval_pderiv_ne_zero (i : Fin 2)
    (hi : MvPolynomial.pderiv i C.equation ≠ 0) :
    C.eval (MvPolynomial.pderiv i C.equation) ≠ 0 := by
  intro hzero
  have hmk : C.toCoordinateRing (MvPolynomial.pderiv i C.equation) = 0 :=
    (IsFractionRing.injective C.coordinateRing C.FunctionField) (by simpa using hzero)
  have hdiv : C.equation ∣ MvPolynomial.pderiv i C.equation :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hmk)
  have hdegree := pderiv_totalDegree_lt C.equation i hi
  have hdegree' := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hi
  omega

/-- **Stacks 09U0.** At least one of the two partial derivatives of an irreducible plane
equation over a perfect field is nonzero in the function field of the curve it cuts out.
This is what makes the differential `ω = dx/f_y = -dy/f_x` well defined. -/
@[stacks 09U0 "well-definedness of ω: a partial derivative survives"]
theorem partialX_ne_zero_or_partialY_ne_zero [PerfectField k] :
    C.partialX ≠ 0 ∨ C.partialY ≠ 0 :=
  (pderivs_not_both_zero C.irreducible_equation).imp
    (C.eval_pderiv_ne_zero 0) (C.eval_pderiv_ne_zero 1)

/-! ### The two coordinate differentials -/

private theorem D_coordinate_ne_zero :
    (C.partialY ≠ 0 → KaehlerDifferential.D k C.FunctionField C.x ≠ 0) ∧
      (C.partialX ≠ 0 → KaehlerDifferential.D k C.FunctionField C.y ≠ 0) := by
  let P := MvPolynomial (Fin 2) k
  let A := C.coordinateRing
  let K := C.FunctionField
  let I : Ideal P := C.ideal
  let φ : P →ₐ[k] A := Ideal.Quotient.mkₐ k I
  let dP : Derivation k P P :=
    (MvPolynomial.pderiv 1 C.equation) • MvPolynomial.pderiv 0 -
      (MvPolynomial.pderiv 0 C.equation) • MvPolynomial.pderiv 1
  have hdf : dP C.equation = 0 := by
    simp [dP, smul_eq_mul]
    ring
  have hkill (q : P) (hq : φ q = 0) : φ (dP q) = 0 := by
    obtain ⟨r, rfl⟩ := (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hq))
    rw [dP.leibniz, hdf, smul_zero, add_zero]
    show φ C.equation * φ (dP r) = 0
    have hf : φ C.equation = 0 := by
      show Ideal.Quotient.mk I C.equation = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simp [hf]
  let dA : Derivation k A A :=
    Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective k I) hkill
  have hdA_apply (q : P) : dA (φ q) = φ (dP q) :=
    Derivation.liftOfSurjective_apply (Ideal.Quotient.mkₐ_surjective k I) hkill q
  let L : Ω[A⁄k] →ₗ[A] A := dA.liftKaehlerDifferential
  let Lk : Ω[A⁄k] →ₗ[A] K := (IsScalarTower.toAlgHom A A K).toLinearMap.comp L
  let Λ : K ⊗[A] Ω[A⁄k] →ₗ[K] K :=
    (Algebra.TensorProduct.lmul'' A).toLinearMap.comp (Lk.baseChange K)
  let _ : Algebra.FormallyEtale A K :=
    Algebra.FormallyEtale.of_isLocalization (M := nonZeroDivisors A)
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A K
  let Ψ : Ω[K⁄k] →ₗ[K] K := Λ.comp e.symm.toLinearMap
  have hdAx : dA (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2))) =
      φ (MvPolynomial.pderiv 1 C.equation) := by
    show dA (φ (MvPolynomial.X (0 : Fin 2))) = _
    rw [hdA_apply]
    simp only [Fin.isValue, Derivation.coe_sub, Derivation.coe_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
      mul_zero, sub_zero, map_mul, dP]
    rw [MvPolynomial.pderiv_X_self, map_one, mul_one]
  have hdAy : dA (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2))) =
      -φ (MvPolynomial.pderiv 0 C.equation) := by
    show dA (φ (MvPolynomial.X (1 : Fin 2))) = _
    rw [hdA_apply]
    simp only [Fin.isValue, Derivation.coe_sub, Derivation.coe_smul, Pi.sub_apply,
      Pi.smul_apply, MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul,
      mul_zero, zero_sub, map_neg, map_mul, dP]
    rw [MvPolynomial.pderiv_X_self, map_one, mul_one]
  have hΛ (a : A) : Λ (1 ⊗ₜ[A] KaehlerDifferential.D k A a) = algebraMap A K (dA a) := by
    simp only [Λ, LinearMap.comp_apply, Algebra.TensorProduct.lmul'',
      LinearMap.baseChange_tmul, Lk, L, Derivation.liftKaehlerDifferential_comp_D]
    show (1 : K) * algebraMap A K (dA a) = _
    simp
  have hx : Ψ (KaehlerDifferential.D k K C.x) = C.partialY := by
    show Λ (e.symm (KaehlerDifferential.D k K
      (algebraMap A K (Ideal.Quotient.mk I (MvPolynomial.X (0 : Fin 2)))))) = C.partialY
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, hΛ, hdAx]
    rfl
  have hy : Ψ (KaehlerDifferential.D k K C.y) = -C.partialX := by
    show Λ (e.symm (KaehlerDifferential.D k K
      (algebraMap A K (Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 2)))))) = -C.partialX
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, hΛ, hdAy,
      map_neg]
    rfl
  refine ⟨fun h hzero => h ?_, fun h hzero => h (neg_eq_zero.mp ?_)⟩
  · have hΨ := congrArg Ψ hzero
    rwa [hx, map_zero] at hΨ
  · have hΨ := congrArg Ψ hzero
    rwa [hy, map_zero] at hΨ

private theorem D_eq_pderiv_smul (f : MvPolynomial (Fin 2) k) :
    KaehlerDifferential.D k (MvPolynomial (Fin 2) k) f =
      MvPolynomial.pderiv 0 f •
          KaehlerDifferential.D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 0) +
        MvPolynomial.pderiv 1 f •
          KaehlerDifferential.D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 1) := by
  let b := KaehlerDifferential.mvPolynomialBasis k (Fin 2)
  apply b.repr.injective
  ext i
  fin_cases i <;> simp [b, KaehlerDifferential.mvPolynomialBasis_repr_apply]

/-- The relation `f_x · dx + f_y · dy = 0` in `Ω[K⁄k]`, coming from `d f = 0`. -/
theorem partialX_smul_D_x_add_partialY_smul_D_y_eq_zero :
    C.partialX • KaehlerDifferential.D k C.FunctionField C.x +
      C.partialY • KaehlerDifferential.D k C.FunctionField C.y = 0 := by
  let P := MvPolynomial (Fin 2) k
  let A := C.coordinateRing
  let K := C.FunctionField
  let _ : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq (R := P) (S := A) (A := K)
    fun _ => rfl
  have hmap (q : P) : algebraMap P K q = algebraMap A K (Ideal.Quotient.mk C.ideal q) :=
    IsScalarTower.algebraMap_apply (R := P) (S := A) (A := K) q
  have hφ : algebraMap P K C.equation = 0 := by
    rw [hmap]
    simp [A, AffinePlaneCurve.coordinateRing]
  have hd := KaehlerDifferential.map_D k k P K C.equation
  rw [hφ, map_zero] at hd
  have htensor (p : P) (ω : Ω[P⁄k]) :
      (1 : K) ⊗ₜ[P] (p • ω) = (algebraMap P K p) • ((1 : K) ⊗ₜ[P] ω) := by
    calc (1 : K) ⊗ₜ[P] (p • ω) = (p • (1 : K)) ⊗ₜ[P] ω := by
          rw [TensorProduct.tmul_smul]
          exact TensorProduct.smul_tmul' p 1 ω
      _ = (algebraMap P K p) ⊗ₜ[P] ω := by rw [Algebra.algebraMap_eq_smul_one]
      _ = (algebraMap P K p) • ((1 : K) ⊗ₜ[P] ω) := by
          rw [TensorProduct.smul_tmul']
          congr 1
          simp
  have hzero : KaehlerDifferential.mapBaseChange k P K
      ((1 : K) ⊗ₜ[P] KaehlerDifferential.D k P C.equation) = 0 := by
    rw [KaehlerDifferential.mapBaseChange_tmul]
    simpa using hd
  rw [D_eq_pderiv_smul, TensorProduct.tmul_add] at hzero
  simp_rw [htensor, map_add, map_smul, KaehlerDifferential.mapBaseChange_tmul, one_smul] at hzero
  rwa [KaehlerDifferential.map_D k k P K (MvPolynomial.X 0),
    KaehlerDifferential.map_D k k P K (MvPolynomial.X 1), hmap, hmap, hmap, hmap] at hzero

/-- **Stacks 09U0.** Where both partial derivatives are nonzero, the two formulas
`dx/f_y` and `-dy/f_x` for the distinguished differential agree. -/
@[stacks 09U0 "well-definedness of ω: the two formulas agree"]
theorem inv_partialY_smul_D_x_eq_neg_inv_partialX_smul_D_y
    (hx : C.partialX ≠ 0) (hy : C.partialY ≠ 0) :
    C.partialY⁻¹ • KaehlerDifferential.D k C.FunctionField C.x =
      -(C.partialX⁻¹ • KaehlerDifferential.D k C.FunctionField C.y) := by
  calc C.partialY⁻¹ • KaehlerDifferential.D k C.FunctionField C.x
      = (C.partialX * C.partialY)⁻¹ •
          (C.partialX • KaehlerDifferential.D k C.FunctionField C.x) := by
        rw [smul_smul, show (C.partialX * C.partialY)⁻¹ * C.partialX = C.partialY⁻¹ by
          field_simp]
    _ = -(C.partialX⁻¹ • KaehlerDifferential.D k C.FunctionField C.y) := by
        have hrel := congrArg ((C.partialX * C.partialY)⁻¹ • ·)
          C.partialX_smul_D_x_add_partialY_smul_D_y_eq_zero
        rw [smul_add, smul_zero, add_eq_zero_iff_eq_neg] at hrel
        rw [hrel, smul_smul, show (C.partialX * C.partialY)⁻¹ * C.partialY = C.partialX⁻¹ by
          field_simp]

/-- **Stacks 09U0.** If the partial derivative with respect to `y` is nonzero, then
`dx/f_y` is a nonzero differential. -/
@[stacks 09U0 "well-definedness of ω: dx/f_y is nonzero"]
theorem inv_partialY_smul_D_x_ne_zero (hy : C.partialY ≠ 0) :
    C.partialY⁻¹ • KaehlerDifferential.D k C.FunctionField C.x ≠ 0 :=
  smul_ne_zero (inv_ne_zero hy) ((C.D_coordinate_ne_zero).1 hy)

/-- **Stacks 09U0.** If the partial derivative with respect to `x` is nonzero, then
`-dy/f_x` is a nonzero differential. -/
@[stacks 09U0 "well-definedness of ω: -dy/f_x is nonzero"]
theorem neg_inv_partialX_smul_D_y_ne_zero (hx : C.partialX ≠ 0) :
    -(C.partialX⁻¹ • KaehlerDifferential.D k C.FunctionField C.y) ≠ 0 :=
  neg_ne_zero.mpr (smul_ne_zero (inv_ne_zero hx) ((C.D_coordinate_ne_zero).2 hx))

/-! ### The distinguished differential -/

/-- **Stacks 09U0.** The distinguished rational differential `ω = dx/f_y = -dy/f_x` of an
irreducible affine plane curve. -/
@[stacks 09U0 "the differential ω"]
def differential : Ω[C.FunctionField⁄k] :=
  let : Decidable (C.partialY ≠ 0) := Classical.propDecidable _
  if C.partialY ≠ 0 then C.partialY⁻¹ • KaehlerDifferential.D k C.FunctionField C.x
  else -(C.partialX⁻¹ • KaehlerDifferential.D k C.FunctionField C.y)

/-- Wherever `f_y` is nonzero, the distinguished differential is `dx/f_y`. -/
theorem differential_eq_inv_partialY_smul_D_x (hy : C.partialY ≠ 0) :
    C.differential = C.partialY⁻¹ • KaehlerDifferential.D k C.FunctionField C.x :=
  ite_eq_left hy

/-- Wherever `f_x` is nonzero, the distinguished differential is `-dy/f_x`. -/
theorem differential_eq_neg_inv_partialX_smul_D_y (hx : C.partialX ≠ 0) :
    C.differential = -(C.partialX⁻¹ • KaehlerDifferential.D k C.FunctionField C.y) := by
  by_cases hy : C.partialY ≠ 0
  · exact (C.differential_eq_inv_partialY_smul_D_x hy).trans
      (C.inv_partialY_smul_D_x_eq_neg_inv_partialX_smul_D_y hx hy)
  · exact ite_eq_right hy

/-- **Stacks 09U0.** The distinguished differential of an irreducible plane curve over a
perfect field is nonzero. -/
@[stacks 09U0 "ω is nonzero"]
theorem differential_ne_zero [PerfectField k] : C.differential ≠ 0 := by
  by_cases hy : C.partialY ≠ 0
  · rw [C.differential_eq_inv_partialY_smul_D_x hy]
    exact C.inv_partialY_smul_D_x_ne_zero hy
  · have hx : C.partialX ≠ 0 := C.partialX_ne_zero_or_partialY_ne_zero.resolve_right hy
    rw [C.differential_eq_neg_inv_partialX_smul_D_y hx]
    exact C.neg_inv_partialX_smul_D_y_ne_zero hx

end AffinePlaneCurve

/-! ### The projective plane curve -/

/-- **Stacks 09U0.** An irreducible projective plane curve `D = V(F)` over a field, together
with the affine plane curve cut out on the standard chart `X₀ = 1` by the dehomogenization
`f(x, y) = F(1, x, y)`.

The irreducibility of the dehomogenization is carried as a field rather than deduced from the
irreducibility of `F` and the assumption that `F` is not a scalar multiple of the first
coordinate. -/
@[stacks 09U0 "the plane-curve situation"]
structure ProjectivePlaneCurve (k : Type u) [Field k] where
  /-- The homogeneous equation `F` of the curve. -/
  equation : MvPolynomial (Fin 3) k
  /-- The degree `d` of the homogeneous equation. -/
  degree : ℕ
  /-- The equation is irreducible. -/
  irreducible_equation : Irreducible equation
  /-- The equation is homogeneous of degree `d`. -/
  isHomogeneous_equation : equation.IsHomogeneous degree
  /-- The equation is not a scalar multiple of the first homogeneous coordinate, so that the
  curve is not the line at infinity and its standard chart is nonempty. -/
  not_smul_X₀ : ∀ a : k, equation ≠ MvPolynomial.C a * MvPolynomial.X (0 : Fin 3)
  /-- The affine plane curve cut out on the standard chart. -/
  affineChart : AffinePlaneCurve k
  /-- The equation of the standard chart is the dehomogenization `F(1, x, y)`. -/
  affineChart_equation : affineChart.equation =
    MvPolynomial.aeval ![1, MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)] equation

namespace ProjectivePlaneCurve

variable {k : Type u} [Field k] (D : ProjectivePlaneCurve k)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective plane over the base field, as the `Proj` of its homogeneous coordinate
ring in three variables. -/
def projectivePlane (_D : ProjectivePlaneCurve k) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)

/-- The vanishing set of the homogeneous equation, as a set of points of the projective
plane. -/
def zeroLocus (D : ProjectivePlaneCurve k) :
    Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3) k)) :=
  ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 3) k)
    ({D.equation} : Set (MvPolynomial (Fin 3) k))

/-- The vanishing set of the homogeneous equation, as a closed subset of the projective
plane. -/
def closedLocus : TopologicalSpace.Closeds D.projectivePlane :=
  ⟨D.zeroLocus, ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

/-- **Stacks 09U0.** The projective plane curve `D = V(F)`, as the reduced induced closed
subscheme of the projective plane on the vanishing set of `F`. -/
@[stacks 09U0 "the projective plane curve D = V(F)"]
def curve : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal D.closedLocus).subscheme

/-- **Stacks 09U0.** The closed immersion of the projective plane curve into the projective
plane. -/
@[stacks 09U0 "the closed immersion of D into the projective plane"]
def inclusion : D.curve ⟶ D.projectivePlane :=
  (Scheme.IdealSheafData.vanishingIdeal D.closedLocus).subschemeι

/-- **Stacks 09U0.** The distinguished rational differential `ω = dx/f_y = -dy/f_x` of the
plane curve, taken on its standard affine chart. -/
@[stacks 09U0 "the differential ω of the plane curve"]
def differential : Ω[D.affineChart.FunctionField⁄k] := D.affineChart.differential

end ProjectivePlaneCurve

end AlgebraicGeometry

end
