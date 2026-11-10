module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.FieldTheory.MvRatFunc.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.RingTheory.UniqueFactorizationDomain.Basic

/-!
# A variety that is not geometrically reduced

Over the rational function field `𝔽ₚ(s,t)`, the plane hypersurface `1 + s xᵖ + t yᵖ = 0` is a
variety. After an extension containing `p`-th roots of `s` and `t`, its defining equation becomes
a `p`-th power, so the base change is not reduced.

## Main definitions

* `AlgebraicGeometry.InseparableHypersurface.rationalFunctionField` is `𝔽ₚ(s,t)`.
* `AlgebraicGeometry.InseparableHypersurface.hypersurfaceRing` is the coordinate ring of the
  plane hypersurface.
* `AlgebraicGeometry.InseparableHypersurface.nilpotentElement` is the class of
  `1 + s¹ᐟᵖ x + t¹ᐟᵖ y` after extension.

## Main results

* `AlgebraicGeometry.InseparableHypersurface.hypersurface_isVariety` states that the hypersurface
  is a variety.
* `AlgebraicGeometry.InseparableHypersurface.nilpotentElement_pow_eq_zero` and
  `AlgebraicGeometry.InseparableHypersurface.nilpotentElement_ne_zero` describe the nonzero
  nilpotent element after extension.
* `AlgebraicGeometry.InseparableHypersurface.baseChange_not_isReduced` states that every such
  base change is nonreduced.

## Implementation notes

The two transcendental generators and the two polynomial coordinates are indexed by `Fin 2`. The
nonreducedness statement uses the canonical scheme pullback; the two element statements use its
affine coordinate-ring presentation.

Irreducibility of the defining equation is obtained by viewing it as an Eisenstein polynomial in
`x` over the one-variable polynomial ring in `y`, whose constant term `1 + t yᵖ` generates a
prime ideal because `tᵖ` has no `p`-th root in `𝔽ₚ(s,t)`.

The declarations are grouped in a namespace of their own because they name the pieces of one
example scheme, and leaf names such as `nilpotentElement` and `extendedRing` are too generic to
sit directly in `AlgebraicGeometry`.

## References

* [Stacks Project, Tag 020F](https://stacks.math.columbia.edu/tag/020F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.InseparableHypersurface

variable (p : ℕ) [Fact p.Prime]

/-- The rational function field `𝔽ₚ(s,t)`. -/
public abbrev rationalFunctionField := MvRatFunc (Fin 2) (ZMod p)

/-- The `i`-th transcendental generator of `𝔽ₚ(s,t)`. -/
public noncomputable def transcendentalGenerator (i : Fin 2) : rationalFunctionField p :=
  algebraMap (MvPolynomial (Fin 2) (ZMod p)) (rationalFunctionField p) (MvPolynomial.X i)

/-- The equation `1 + s xᵖ + t yᵖ`. -/
public noncomputable def hypersurfaceEquation :
    MvPolynomial (Fin 2) (rationalFunctionField p) :=
  1 + MvPolynomial.C (transcendentalGenerator p 0) * MvPolynomial.X 0 ^ p +
    MvPolynomial.C (transcendentalGenerator p 1) * MvPolynomial.X 1 ^ p

/-- The coordinate ring of the example. -/
public abbrev hypersurfaceRing :=
  MvPolynomial (Fin 2) (rationalFunctionField p) ⧸
    Ideal.span ({hypersurfaceEquation p} : Set (MvPolynomial (Fin 2) (rationalFunctionField p)))

/-- The structure morphism of the hypersurface over `𝔽ₚ(s,t)`. -/
public noncomputable def hypersurfaceToSpec :
    Spec (.of (hypersurfaceRing p)) ⟶ Spec (.of (rationalFunctionField p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (rationalFunctionField p) (hypersurfaceRing p)))

/-- The same hypersurface equation over an extension field. -/
public noncomputable def extendedEquation (K : Type*) [Field K]
    [Algebra (rationalFunctionField p) K] : MvPolynomial (Fin 2) K :=
  1 + MvPolynomial.C (algebraMap (rationalFunctionField p) K
      (transcendentalGenerator p 0)) * MvPolynomial.X 0 ^ p +
    MvPolynomial.C (algebraMap (rationalFunctionField p) K
      (transcendentalGenerator p 1)) * MvPolynomial.X 1 ^ p

/-- The coordinate ring of the extended hypersurface. -/
public abbrev extendedRing (K : Type*) [Field K]
    [Algebra (rationalFunctionField p) K] :=
  MvPolynomial (Fin 2) K ⧸
    Ideal.span ({extendedEquation p K} : Set (MvPolynomial (Fin 2) K))

/-- The class of `1 + a x + b y` in the extended coordinate ring. -/
public noncomputable def nilpotentElement (K : Type*) [Field K]
    [Algebra (rationalFunctionField p) K] (a b : K) : extendedRing p K :=
  Ideal.Quotient.mk _
    (1 + MvPolynomial.C a * MvPolynomial.X 0 +
      MvPolynomial.C b * MvPolynomial.X 1)

/-- **Stacks Project, Tag 020F.** The displayed element is nilpotent. -/
@[stacks 020F "the displayed element has p-th power zero"]
public theorem nilpotentElement_pow_eq_zero (K : Type*) [Field K]
    [Algebra (rationalFunctionField p) K] (a b : K)
    (ha : a ^ p = algebraMap (rationalFunctionField p) K (transcendentalGenerator p 0))
    (hb : b ^ p = algebraMap (rationalFunctionField p) K (transcendentalGenerator p 1)) :
    nilpotentElement p K a b ^ p = 0 := by
  let R := MvPolynomial (Fin 2) K
  let g : R := 1 + MvPolynomial.C a * MvPolynomial.X 0 +
    MvPolynomial.C b * MvPolynomial.X 1
  change Ideal.Quotient.mk _ g ^ p = 0
  rw [← map_pow (Ideal.Quotient.mk _)]
  let : CharP K p := charP_of_injective_algebraMap
    (algebraMap (rationalFunctionField p) K).injective p
  let : CharP R p := inferInstance
  rw [show g ^ p = 1 + MvPolynomial.C (a ^ p) * MvPolynomial.X 0 ^ p +
      MvPolynomial.C (b ^ p) * MvPolynomial.X 1 ^ p by
        dsimp [g]
        rw [add_pow_char, add_pow_char]
        simp only [one_pow, mul_pow, MvPolynomial.C_pow]]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp [extendedEquation, ha, hb])

private theorem transcendentalGenerator_ne_zero (p : ℕ) [Fact p.Prime]
    (i : Fin 2) : transcendentalGenerator p i ≠ 0 := by
  intro h
  simp [transcendentalGenerator] at h

private theorem transcendentalGenerator_one_not_pth_power (p : ℕ) [Fact p.Prime] :
    ∀ b : rationalFunctionField p, b ^ p ≠ transcendentalGenerator p 1 := by
  intro b hb
  let P := MvPolynomial (Fin 2) (ZMod p)
  obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective P b
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hden : algebraMap P (rationalFunctionField p) v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective P (rationalFunctionField p))).2 hv0
  have hcross :
      (algebraMap P (rationalFunctionField p) u) ^ p =
        algebraMap P (rationalFunctionField p) (MvPolynomial.X 1) *
          (algebraMap P (rationalFunctionField p) v) ^ p := by
    rw [div_pow] at hb
    exact (div_eq_iff (pow_ne_zero p hden)).mp hb
  have hpoly : u ^ p = (MvPolynomial.X 1 : P) * v ^ p := by
    apply IsFractionRing.injective P (rationalFunctionField p)
    simpa [map_mul, map_pow] using hcross
  have hu : u ≠ 0 := by
    intro huzero
    have hxv : (MvPolynomial.X 1 : P) * v ^ p ≠ 0 :=
      mul_ne_zero (MvPolynomial.X_ne_zero 1) (pow_ne_zero p hv0)
    rw [huzero, zero_pow (Fact.out : Nat.Prime p).ne_zero] at hpoly
    exact hxv hpoly.symm
  have heq : (p * (MvPolynomial.degreeOf (1 : Fin 2) u)) =
      1 + p * (MvPolynomial.degreeOf (1 : Fin 2) v) := by
    have h := congrArg (MvPolynomial.degreeOf (1 : Fin 2)) hpoly
    rw [MvPolynomial.degreeOf_pow_eq _ _ _ hu,
      MvPolynomial.degreeOf_mul_eq (MvPolynomial.X_ne_zero 1) (pow_ne_zero p hv0),
      MvPolynomial.degreeOf_X_self, MvPolynomial.degreeOf_pow_eq _ _ _ hv0] at h
    simpa [Nat.mul_comm] using h
  have hmod := congrArg (fun n : ℕ => n % p) heq
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  norm_num [Nat.mul_mod, Nat.add_mod, hp] at hmod
  omega

private theorem planePolynomial_irreducible (p : ℕ) [Fact p.Prime] :
    Irreducible (1 + Polynomial.C (transcendentalGenerator p 1) *
      (Polynomial.X : Polynomial (rationalFunctionField p)) ^ p) := by
  let k := rationalFunctionField p
  let t := transcendentalGenerator p 1
  let q : Polynomial k := 1 + Polynomial.C t * Polynomial.X ^ p
  have ht : t ≠ 0 := transcendentalGenerator_ne_zero p 1
  have hroot : ∀ z : k, z ^ p ≠ -1 / t := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow (Fact.out : Nat.Prime p).ne_zero] at hz
      exact (div_ne_zero (by norm_num) ht) hz.symm
    have hpow : (-z⁻¹) ^ p = t := by
      calc
        (-z⁻¹) ^ p = -((z ^ p)⁻¹) := by
          rw [neg_pow, neg_one_pow_char, inv_pow]
          ring
        _ = t := by
          rw [hz]
          field
    exact (transcendentalGenerator_one_not_pth_power p (-z⁻¹)) hpow
  have hcore : Irreducible (Polynomial.X ^ p - Polynomial.C (-1 / t : k)) :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p) hroot
  have htunit : IsUnit (Polynomial.C t : Polynomial k) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ht)
  have hmul : Polynomial.C t * Polynomial.C (-1 / t : k) = -1 := by
    calc
      Polynomial.C t * Polynomial.C (-1 / t : k) = Polynomial.C (t * (-1 / t)) := by
        rw [← map_mul]
      _ = Polynomial.C (-1) := by
        congr 1
        field_simp [ht]
      _ = -1 := by simp
  have hq : q = Polynomial.C t *
      (Polynomial.X ^ p - Polynomial.C (-1 / t : k)) := by
    dsimp [q]
    rw [mul_sub, hmul]
    ring
  rw [show (1 + Polynomial.C (transcendentalGenerator p 1) *
      (Polynomial.X : Polynomial k) ^ p) = q from rfl, hq]
  exact (associated_unit_mul_left _ _ htunit).symm.irreducible hcore

private theorem planePolynomial_in_y_irreducible (p : ℕ) [Fact p.Prime] :
    Irreducible (1 + MvPolynomial.C (transcendentalGenerator p 1) *
      (MvPolynomial.X 0 : MvPolynomial (Fin 1) (rationalFunctionField p)) ^ p) := by
  let e := MvPolynomial.uniqueAlgEquiv (rationalFunctionField p) (Fin 1)
  apply (MulEquiv.irreducible_iff e.toRingEquiv).mp
  simpa [e, MvPolynomial.uniqueAlgEquiv] using planePolynomial_irreducible p

private theorem hypersurfaceEquation_irreducible (p : ℕ) [Fact p.Prime] :
    Irreducible (hypersurfaceEquation p) := by
  let k := rationalFunctionField p
  let B := MvPolynomial (Fin 1) k
  let s : B := MvPolynomial.C (transcendentalGenerator p 0)
  let q := 1 + MvPolynomial.C (transcendentalGenerator p 1) *
    (MvPolynomial.X 0 : B) ^ p
  let f : Polynomial B := Polynomial.C s * Polynomial.X ^ p + Polynomial.C q
  have hsunit : IsUnit s :=
    (isUnit_iff_ne_zero.mpr (transcendentalGenerator_ne_zero p 0)).map (algebraMap k B)
  have hqprime : Prime q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (planePolynomial_in_y_irreducible p)
  let P : Ideal B := Ideal.span {q}
  have hPprime : P.IsPrime := (Ideal.span_singleton_prime hqprime.ne_zero).2 hqprime
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hnat : f.natDegree = p := by
    have hterm : (Polynomial.C s * Polynomial.X ^ p).natDegree = p := by
      rw [Polynomial.natDegree_C_mul_of_isUnit hsunit, Polynomial.natDegree_X_pow]
    have hconst : (Polynomial.C q : Polynomial B).natDegree = 0 := by simp
    dsimp [f]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact hterm
    · rwa [hconst, hterm]
  have hcoef : ∀ n, f.coeff n = (if n = p then s else 0) + (if n = 0 then q else 0) := fun n => by
    simp only [f, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
  have hcoeff : f.coeff p = s := by simp [hcoef, hp.ne']
  have hzero : f.coeff 0 = q := by simp [hcoef, hp.ne]
  have hlead : f.leadingCoeff = s := by
    rwa [Polynomial.leadingCoeff, hnat]
  have hfprim : f.IsPrimitive := by
    rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
    intro r hr
    have hc := (Polynomial.C_dvd_iff_dvd_coeff r f).mp hr p
    rw [hcoeff] at hc
    exact isUnit_of_dvd_unit hc hsunit
  have hfE : f.IsEisensteinAt P := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hlead]
      exact fun hsP => hPprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hsP hsunit)
    · intro n hn
      have hn' : n < p := by simpa [hnat] using hn
      by_cases hn0 : n = 0
      · subst n
        rw [hzero]
        exact Ideal.subset_span (Set.mem_singleton q)
      · simp [hcoef, hn0, Nat.ne_of_lt hn']
    · intro hqP2
      rw [hzero] at hqP2
      change q ∈ (Ideal.span {q} : Ideal B) ^ 2 at hqP2
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hqP2
      obtain ⟨u, hu⟩ := hqP2
      have hu' : u * q = 1 :=
        mul_right_cancel₀ hqprime.ne_zero (by linear_combination hu)
      exact hqprime.not_isUnit (isUnit_of_dvd_one ⟨u, by rw [mul_comm q u, hu']⟩)
  have hfIrr : Irreducible f := hfE.irreducible hPprime hfprim (by simpa [hnat] using hp)
  let e := MvPolynomial.finSuccEquiv k 1
  have he : e (hypersurfaceEquation p) = f := by
    change e (1 + MvPolynomial.C (transcendentalGenerator p 0) *
        MvPolynomial.X 0 ^ p + MvPolynomial.C (transcendentalGenerator p 1) *
        MvPolynomial.X 1 ^ p) =
      Polynomial.C (MvPolynomial.C (transcendentalGenerator p 0)) * Polynomial.X ^ p +
        Polynomial.C (1 + MvPolynomial.C (transcendentalGenerator p 1) *
          (MvPolynomial.X 0 : B) ^ p)
    have hx0 : e (MvPolynomial.X (0 : Fin 2)) = (Polynomial.X : Polynomial B) :=
      MvPolynomial.finSuccEquiv_X_zero
    have hx1 : e (MvPolynomial.X (1 : Fin 2)) =
        Polynomial.C (MvPolynomial.X (0 : Fin 1) : B) := by
      simpa only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by decide] using
        (MvPolynomial.finSuccEquiv_X_succ (R := k) (n := 1) (j := 0))
    have hC : ∀ c : k, e (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := fun c => by
      change e (algebraMap k (MvPolynomial (Fin 2) k) c) = _
      rw [e.commutes]
      simp [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    simp only [map_add, map_one, map_mul, map_pow, hx0, hx1, hC]
    ring_nf
  exact (MulEquiv.irreducible_iff e.toRingEquiv (x := hypersurfaceEquation p)).mp
    (he ▸ hfIrr)

/-- **Stacks Project, Tag 020F.** The hypersurface over `𝔽ₚ(s,t)` is a variety. -/
@[stacks 020F "the original scheme is a variety"]
public theorem hypersurface_isVariety :
    IsVariety (rationalFunctionField p) (hypersurfaceToSpec p) := by
  let k := rationalFunctionField p
  let f := hypersurfaceEquation p
  have hf : Irreducible f := hypersurfaceEquation_irreducible p
  have : (Ideal.span ({f} : Set (MvPolynomial (Fin 2) k))).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)
  let : IsDomain (hypersurfaceRing p) := inferInstance
  have : IsIntegral (Spec (.of (hypersurfaceRing p))) := inferInstance
  have : IsSeparated (hypersurfaceToSpec p) := inferInstance
  have : Algebra.FiniteType k (hypersurfaceRing p) := by
    dsimp [hypersurfaceRing]
    infer_instance
  have : LocallyOfFiniteType (hypersurfaceToSpec p) := by
    change LocallyOfFiniteType (Spec (.of (hypersurfaceRing p)) ↘ Spec (.of k))
    infer_instance
  have : IsAffineHom (hypersurfaceToSpec p) := inferInstance
  have : QuasiCompact (hypersurfaceToSpec p) := inferInstance
  exact IsVariety.mk

private noncomputable def baseChangeCoordinateRingEquiv (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra (rationalFunctionField p) K] :
    (hypersurfaceRing p) ⊗[(rationalFunctionField p)] K ≃+* extendedRing p K := by
  let k := rationalFunctionField p
  let A := MvPolynomial (Fin 2) k
  let I : Ideal A := Ideal.span {hypersurfaceEquation p}
  let I' : Ideal (A ⊗[k] K) := I.map (algebraMap A (A ⊗[k] K))
  let J : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {extendedEquation p K}
  let e : A ⊗[k] K ≃+* MvPolynomial (Fin 2) K :=
    (Algebra.TensorProduct.comm k A K).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv
  have hgen : e (algebraMap A (A ⊗[k] K) (hypersurfaceEquation p)) =
      extendedEquation p K := by
    calc
      _ = e (hypersurfaceEquation p ⊗ₜ[k] (1 : K)) := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      _ = MvPolynomial.map (algebraMap k K) (hypersurfaceEquation p) := by
        change MvPolynomial.algebraTensorAlgEquiv k K
          (1 ⊗ₜ[k] hypersurfaceEquation p) = _
        rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
        simp
      _ = extendedEquation p K := by
        simp [k, hypersurfaceEquation, extendedEquation, rationalFunctionField,
          MvPolynomial.map_C, MvPolynomial.map_X]
  have hIJ : J = I'.map e.toRingHom := by
    change Ideal.span {extendedEquation p K} =
      (I.map (algebraMap A (A ⊗[k] K))).map e.toRingHom
    rw [Ideal.map_map]
    dsimp [I, J]
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span {extendedEquation p K} =
      Ideal.span {e (algebraMap A (A ⊗[k] K) (hypersurfaceEquation p))}
    exact congrArg (fun x : MvPolynomial (Fin 2) K => Ideal.span ({x} : Set _)) hgen.symm
  letI : CommRing (A ⊗[k] K) := inferInstance
  let eQuot : (A ⊗[k] K) ⧸ I' ≃+* (MvPolynomial (Fin 2) K) ⧸ J :=
    Ideal.quotientEquiv I' J e hIJ
  exact (Algebra.TensorProduct.quotientTensorEquiv (R := k) k K A I).toRingEquiv.trans eQuot

private theorem planeEquation_degreeOf_x {R : Type*} [Field R] (p : ℕ) [Fact p.Prime]
    (s t : R) (hs : s ≠ 0) :
    (1 + MvPolynomial.C s * MvPolynomial.X 0 ^ p +
      MvPolynomial.C t * MvPolynomial.X 1 ^ p : MvPolynomial (Fin 2) R).degreeOf 0 = p := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hterm :
      (MvPolynomial.C s * MvPolynomial.X 0 ^ p : MvPolynomial (Fin 2) R).degreeOf 0 = p := by
    rw [MvPolynomial.degreeOf_C_mul _ _ (mem_nonZeroDivisors_iff_ne_zero.mpr hs)]
    simp
  have hother :
      (MvPolynomial.C t * MvPolynomial.X 1 ^ p : MvPolynomial (Fin 2) R).degreeOf 0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      _ ≤ (MvPolynomial.X 1 ^ p : MvPolynomial (Fin 2) R).degreeOf 0 :=
        MvPolynomial.degreeOf_C_mul_le _ _ _
      _ = 0 := MvPolynomial.degreeOf_X_pow_of_ne p (by decide)
  have hfirst :
      ((1 : MvPolynomial (Fin 2) R) + MvPolynomial.C s * MvPolynomial.X 0 ^ p).degreeOf 0 = p := by
    rw [add_comm, MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (i := (0 : Fin 2)) (p :=
      MvPolynomial.C s * MvPolynomial.X 0 ^ p) (q := 1) (by
        rw [hterm]
        simpa using hp)]
    exact hterm
  rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (p :=
    (1 : MvPolynomial (Fin 2) R) + MvPolynomial.C s * MvPolynomial.X 0 ^ p)
    (i := (0 : Fin 2)) (q := MvPolynomial.C t * MvPolynomial.X 1 ^ p)
    (by rwa [hfirst, hother])]
  exact hfirst

private theorem nilpotentPolynomial_totalDegree_le_one {K : Type*} [Field K] (a b : K) :
    (1 + MvPolynomial.C a * MvPolynomial.X 0 +
      MvPolynomial.C b * MvPolynomial.X 1 : MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
  have hterm : ∀ (c : K) (i : Fin 2),
      (MvPolynomial.C c * MvPolynomial.X i : MvPolynomial (Fin 2) K).totalDegree ≤ 1 :=
    fun c i => (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  have hsum : (1 + MvPolynomial.C a * MvPolynomial.X 0 : MvPolynomial (Fin 2) K).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) (hterm a 0))
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le hsum (hterm b 1))

private theorem quotient_mk_ne_zero_of_totalDegree_lt {K : Type*} [Field K]
    {f g : MvPolynomial (Fin 2) K} (hg : g ≠ 0) (hdeg : g.totalDegree < f.totalDegree) :
    Ideal.Quotient.mk (Ideal.span ({f} : Set (MvPolynomial (Fin 2) K))) g ≠ 0 := by
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem] at h
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h
  have hdiv : f ∣ g := ⟨q, by simpa [mul_comm] using hq.symm⟩
  have := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hg
  omega

/-- **Stacks Project, Tag 020F.** The displayed element is nonzero. -/
@[stacks 020F "the displayed element is nonzero"]
public theorem nilpotentElement_ne_zero (K : Type*) [Field K]
    [Algebra (rationalFunctionField p) K] (a b : K) :
    nilpotentElement p K a b ≠ 0 := by
  apply quotient_mk_ne_zero_of_totalDegree_lt
  · intro h
    have h0 : MvPolynomial.eval (fun _ : Fin 2 => (0 : K))
        (1 + MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K) = 1 := by simp
    rw [h] at h0
    simp at h0
  · change (1 + MvPolynomial.C a * MvPolynomial.X 0 +
      MvPolynomial.C b * MvPolynomial.X 1 : MvPolynomial (Fin 2) K).totalDegree <
      (extendedEquation p K).totalDegree
    unfold extendedEquation
    have hs : algebraMap (rationalFunctionField p) K (transcendentalGenerator p 0) ≠ 0 :=
      (map_ne_zero _).2 (transcendentalGenerator_ne_zero p 0)
    have hdegree := planeEquation_degreeOf_x p
      (algebraMap (rationalFunctionField p) K (transcendentalGenerator p 0))
      (algebraMap (rationalFunctionField p) K (transcendentalGenerator p 1)) hs
    exact (nilpotentPolynomial_totalDegree_le_one a b).trans_lt
      ((Fact.out : p.Prime).one_lt.trans_le
        (hdegree.symm.le.trans (MvPolynomial.degreeOf_le_totalDegree _ 0)))

@[instance_reducible] private noncomputable def hypersurfaceRingCommRing
    (p : ℕ) [Fact p.Prime] : CommRing (hypersurfaceRing p) := by
  change CommRing
    (MvPolynomial (Fin 2) (rationalFunctionField p) ⧸
      Ideal.span ({hypersurfaceEquation p} : Set
        (MvPolynomial (Fin 2) (rationalFunctionField p))))
  infer_instance

@[instance_reducible] private noncomputable def baseChangeTensorCommRing
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Algebra (rationalFunctionField p) K] :
    CommRing ((hypersurfaceRing p) ⊗[(rationalFunctionField p)] K) := by
  letI : CommRing (hypersurfaceRing p) := hypersurfaceRingCommRing p
  infer_instance

/-- **Stacks Project, Tag 020F.** The base change to a field containing both roots is
not reduced. -/
@[stacks 020F "the base change is not reduced"]
public theorem baseChange_not_isReduced (K : Type) [Field K]
    [Algebra (rationalFunctionField p) K] (a b : K)
    (ha : a ^ p = algebraMap (rationalFunctionField p) K (transcendentalGenerator p 0))
    (hb : b ^ p = algebraMap (rationalFunctionField p) K (transcendentalGenerator p 1)) :
    ¬ IsReduced (pullback (hypersurfaceToSpec p)
      (Spec.map (CommRingCat.ofHom (algebraMap (rationalFunctionField p) K)))) := by
  let k := rationalFunctionField p
  let R := hypersurfaceRing p
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : CommRing (R ⊗[k] K) := baseChangeTensorCommRing p K
  let iso : pullback (hypersurfaceToSpec p) g ≅ Spec (.of (R ⊗[k] K)) := pullbackSpecIso k R K
  intro hred
  have hSpec : IsReduced (Spec (.of (R ⊗[k] K))) :=
    @isReduced_of_isOpenImmersion _ _ iso.inv (IsOpenImmersion.of_isIso _) hred
  have hTensor : _root_.IsReduced (R ⊗[k] K) :=
    (affine_isReduced_iff (.of (R ⊗[k] K))).mp hSpec
  have hExtended : _root_.IsReduced (extendedRing p K) :=
    let : _root_.IsReduced (R ⊗[k] K) := hTensor
    isReduced_of_injective (baseChangeCoordinateRingEquiv p K).symm.toRingHom
      (baseChangeCoordinateRingEquiv p K).symm.injective
  have : _root_.IsReduced (extendedRing p K) := hExtended
  exact (nilpotentElement_ne_zero p K a b)
    (eq_zero_of_pow_eq_zero (nilpotentElement_pow_eq_zero p K a b ha hb))

end AlgebraicGeometry.InseparableHypersurface
