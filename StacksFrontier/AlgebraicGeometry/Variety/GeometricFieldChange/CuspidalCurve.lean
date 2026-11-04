module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.RatFunc.Defs
public import Mathlib.FieldTheory.RatFunc.Valuation
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.RingTheory.Derivation.Extension
public import StacksFrontier.RingTheory.Derivation.Regularity

/-!
# A regular geometrically reduced variety that is not geometrically normal

In characteristic `p > 2`, the affine plane curve `y² - xᵖ + t = 0` over the rational function
field `𝔽ₚ(t)` is a regular variety and is geometrically reduced, but it is not geometrically
normal: after adjoining a `p`-th root `t'` of `t` the point `(y, x - t')` becomes a cusp, at
which `y/(x - t')` is integral over the local ring without lying in it.

## Main definitions

* `AlgebraicGeometry.curveEquation`: the defining polynomial `y² - xᵖ + t` over `𝔽ₚ(t)`.
* `AlgebraicGeometry.curveRing`: its coordinate ring `𝔽ₚ(t)[x, y]/(y² - xᵖ + t)`.
* `AlgebraicGeometry.curve`: the affine curve it defines, with structure morphism
  `AlgebraicGeometry.curveToBase`.

## Main results

* `AlgebraicGeometry.curve_isVariety`, `AlgebraicGeometry.curve_isRegular`,
  `AlgebraicGeometry.curve_geometricallyReduced` and
  `AlgebraicGeometry.curve_not_isGeometricallyNormal`: the curve is a variety, is regular, is
  geometrically reduced, and is not geometrically normal.

## Implementation notes

The two variables are indexed by `Fin 2`, with `0` for `x` and `1` for `y`. The prime
characteristic is a parameter, so the example applies to every prime `p > 2`. The four
independent conclusions of the source are stated separately. Regularity is obtained from the
derivation `∂/∂t`, extended to the function field and then to the polynomial ring, which sends
the defining equation to a unit; failure of normality is detected on the base change to the
field of `p`-th roots, where the equation becomes `y² - (x - t')ᵖ`.

## References

* [Stacks Project, Tag 038Y](https://stacks.math.columbia.edu/tag/038Y)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry


variable (p : ℕ) [Fact p.Prime]

/-- The defining equation `y² - xᵖ + t` over `𝔽ₚ(t)`. -/
noncomputable def curveEquation : MvPolynomial (Fin 2) (RatFunc (ZMod p)) :=
  MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
    MvPolynomial.C RatFunc.X

/-- The coordinate ring of the curve `y² - xᵖ + t = 0`. -/
abbrev curveRing :=
  MvPolynomial (Fin 2) (RatFunc (ZMod p)) ⧸ Ideal.span {curveEquation p}

/-- The affine curve `y² - xᵖ + t = 0`. -/
noncomputable abbrev curve : Scheme := Spec (.of (curveRing p))

/-- The canonical structure morphism of the curve over `𝔽ₚ(t)`. -/
noncomputable def curveToBase : curve p ⟶ Spec (.of (RatFunc (ZMod p))) :=
  Spec.map (CommRingCat.ofHom (algebraMap (RatFunc (ZMod p)) (curveRing p)))

private noncomputable def mvPolynomialFinOneEquiv (K : Type*) [CommRing K] :
    MvPolynomial (Fin 1) K ≃+* Polynomial K :=
  (MvPolynomial.finSuccEquiv K 0).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv K (Fin 0)))

private noncomputable def mvPolynomialFinTwoEquiv (K : Type*) [CommRing K] :
    MvPolynomial (Fin 2) K ≃+* Polynomial (Polynomial K) :=
  (MvPolynomial.finSuccEquiv K 1).toRingEquiv.trans
    (Polynomial.mapEquiv (mvPolynomialFinOneEquiv K))

private theorem mvPolynomialFinOneEquiv_X (K : Type*) [CommRing K] :
    mvPolynomialFinOneEquiv K (MvPolynomial.X (0 : Fin 1)) = Polynomial.X := by
  dsimp [mvPolynomialFinOneEquiv]
  rw [Polynomial.mapEquiv_apply, MvPolynomial.finSuccEquiv_X_zero]
  simp

private theorem mvPolynomialFinOneEquiv_C (K : Type*) [CommRing K] (a : K) :
    (mvPolynomialFinOneEquiv K : MvPolynomial (Fin 1) K →+* Polynomial K)
      (MvPolynomial.C a) = Polynomial.C a := by
  dsimp [mvPolynomialFinOneEquiv]
  rw [Polynomial.mapEquiv_apply]
  have hfin : (MvPolynomial.finSuccEquiv K 0) (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by
    simp [MvPolynomial.finSuccEquiv_apply]
  rw [hfin, Polynomial.map_C]
  congr 1
  show MvPolynomial.isEmptyRingEquiv K (Fin 0) (MvPolynomial.C a) = a
  rw [MvPolynomial.isEmptyRingEquiv_eq_coeff_zero]
  simp [MvPolynomial.coeff_C]

private theorem mvPolynomialFinTwoEquiv_X_zero (K : Type*) [CommRing K] :
    mvPolynomialFinTwoEquiv K (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
  show Polynomial.map ((mvPolynomialFinOneEquiv K : MvPolynomial (Fin 1) K →+* Polynomial K))
    ((MvPolynomial.finSuccEquiv K 1) _) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

private theorem mvPolynomialFinTwoEquiv_X_one (K : Type*) [CommRing K] :
    mvPolynomialFinTwoEquiv K (MvPolynomial.X (1 : Fin 2)) = Polynomial.C Polynomial.X := by
  show Polynomial.map ((mvPolynomialFinOneEquiv K : MvPolynomial (Fin 1) K →+* Polynomial K))
    ((MvPolynomial.finSuccEquiv K 1) _) = _
  have hy : (MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X (1 : Fin 2)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 1) (j := (0 : Fin 1)))
  rw [hy, Polynomial.map_C]
  exact congrArg Polynomial.C (mvPolynomialFinOneEquiv_X K)

private theorem mvPolynomialFinTwoEquiv_C (K : Type*) [CommRing K] (a : K) :
    mvPolynomialFinTwoEquiv K (MvPolynomial.C a) = Polynomial.C (Polynomial.C a) := by
  show Polynomial.map ((mvPolynomialFinOneEquiv K : MvPolynomial (Fin 1) K →+* Polynomial K))
    ((MvPolynomial.finSuccEquiv K 1) _) = _
  have hc : (MvPolynomial.finSuccEquiv K 1) (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by
    simp [MvPolynomial.finSuccEquiv_apply]
  rw [hc, Polynomial.map_C, mvPolynomialFinOneEquiv_C]

private theorem curveRing_isRegularRing : IsRegularRing (curveRing p) := by
  let k := RatFunc (ZMod p)
  let : Algebra ℤ k := Ring.toIntAlgebra k
  let B := MvPolynomial (Fin 2) k
  let : CommRing B := inferInstance
  let : Algebra ℤ B := Ring.toIntAlgebra B
  let f : B := curveEquation p
  show IsRegularRing (B ⧸ Ideal.span {f})
  let e : B ≃+* Polynomial (Polynomial k) := mvPolynomialFinTwoEquiv k
  have hxvar : e (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := mvPolynomialFinTwoEquiv_X_zero k
  have hyvar : e (MvPolynomial.X (1 : Fin 2)) = Polynomial.C Polynomial.X :=
    mvPolynomialFinTwoEquiv_X_one k
  have hconst : e (MvPolynomial.C (RatFunc.X : k)) = Polynomial.C (Polynomial.C RatFunc.X) :=
    mvPolynomialFinTwoEquiv_C k _
  let Dk := Stacks.DerivationExtension.locDeriv (Polynomial.derivative'.restrictScalars ℤ)
    (nonZeroDivisors (Polynomial (ZMod p))) k
  have hx : Dk (RatFunc.X) = 1 := by
    rw [show RatFunc.X = algebraMap (Polynomial (ZMod p)) k Polynomial.X from rfl,
      Stacks.DerivationExtension.locDeriv_algebraMap]
    simp [Polynomial.derivative']
  let D1 : Derivation ℤ (Polynomial k) (Polynomial k) :=
    PolynomialModule.equivPolynomialSelf.compDer Dk.mapCoeffs
  let D2 : Derivation ℤ (Polynomial (Polynomial k)) (Polynomial (Polynomial k)) :=
    PolynomialModule.equivPolynomialSelf.compDer D1.mapCoeffs
  have hDF : D2 (Polynomial.C Polynomial.X ^ 2 - Polynomial.X ^ p +
      Polynomial.C (Polynomial.C (RatFunc.X : k))) = 1 := by
    simp [D2, D1, Derivation.mapCoeffs_C, Derivation.mapCoeffs_X, hx]
  have hrel : e f = Polynomial.C Polynomial.X ^ 2 - Polynomial.X ^ p +
      Polynomial.C (Polynomial.C (RatFunc.X : k)) := by
    dsimp [f, curveEquation]
    simp only [map_add, map_sub, map_pow, hyvar, hxvar, hconst]
  let L : B →ₗ[ℤ] B := {
    toFun := fun a => RingEquiv.symm e (D2 (e a))
    map_add' := by intro a b; simp [RingEquiv.map_add]
    map_smul' := by intro z a; simp
  }
  let D : Derivation ℤ B B := Derivation.mk' L (by
    intro a b
    apply e.injective
    dsimp [L]
    rw [map_mul, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, RingEquiv.apply_symm_apply])
  have hD : D f = 1 := by
    show RingEquiv.symm e (D2 (e f)) = 1
    rw [hrel]
    apply e.injective
    simpa using hDF
  let : IsRegularRing B := inferInstance
  apply isRegularRing_quotient_span_singleton_of_isUnit_derivation f D
  simp [hD]

private theorem ratFunc_X_pow_sub_C_not_square (K : Type*) [Field K] (c : K)
    (hp : 2 < p) :
    ∀ b : RatFunc K, b ^ 2 ≠ algebraMap (Polynomial K) (RatFunc K)
      (Polynomial.X ^ p - Polynomial.C c) := by
  classical
  intro b hb
  let v := RatFunc.inftyValuation K
  have hq := Polynomial.X_pow_sub_C_ne_zero (Fact.out : p.Prime).pos c
  have hvq : v (algebraMap (Polynomial K) (RatFunc K)
      (Polynomial.X ^ p - Polynomial.C c)) = WithZero.exp (p : ℤ) := by
    dsimp [v]
    rw [RatFunc.inftyValuation_apply]
    rw [RatFunc.inftyValuation.polynomial (F := K)
      (p := Polynomial.X ^ p - Polynomial.C c) hq]
    simp
  have hpow : v b ^ 2 = WithZero.exp (p : ℤ) := by
    rw [← Valuation.map_pow, hb, hvq]
  have hlog := congrArg WithZero.log hpow
  rw [WithZero.log_pow, WithZero.log_exp] at hlog
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hInt : (2 : ℤ) * WithZero.log (v b) = (p : ℤ) := by
    simpa [nsmul_eq_mul] using hlog
  rcases hpodd with ⟨n, hn⟩
  omega

private theorem irreducible_X_sq_sub_C_X_pow_sub_C (K : Type*) [Field K] (c : K)
    (hp : 2 < p) : Irreducible (Polynomial.X ^ 2 - Polynomial.C (Polynomial.X ^ p -
      Polynomial.C c) : Polynomial (Polynomial K)) := by
  have hmonic : (Polynomial.X ^ 2 - Polynomial.C (Polynomial.X ^ p - Polynomial.C c) :
      Polynomial (Polynomial K)).Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (R := Polynomial K) (K := RatFunc K) hmonic).2
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two
    (by simpa using ratFunc_X_pow_sub_C_not_square p K c hp)

private theorem baseChangedEquation_isDomain (K : Type*) [Field K] (c : K)
    (hp : 2 < p) :
    IsDomain (MvPolynomial (Fin 2) K ⧸ Ideal.span
      {MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
        MvPolynomial.C c}) := by
  let B := MvPolynomial (Fin 2) K
  let R := Polynomial K
  let e : B ≃+* Polynomial R :=
    (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
      (mvPolynomialFinTwoEquiv K)
  have hX0 : e (MvPolynomial.X (0 : Fin 2)) = Polynomial.C Polynomial.X := by
    show mvPolynomialFinTwoEquiv K (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
      (MvPolynomial.X (0 : Fin 2))) = _
    rw [MvPolynomial.rename_X, Equiv.swap_apply_left, mvPolynomialFinTwoEquiv_X_one]
  have hX1 : e (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
    show mvPolynomialFinTwoEquiv K (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
      (MvPolynomial.X (1 : Fin 2))) = _
    rw [MvPolynomial.rename_X, Equiv.swap_apply_right, mvPolynomialFinTwoEquiv_X_zero]
  have hC : e (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
    show mvPolynomialFinTwoEquiv K (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
      (MvPolynomial.C c)) = _
    rw [MvPolynomial.rename_C, mvPolynomialFinTwoEquiv_C]
  let g : Polynomial R := Polynomial.X ^ 2 -
    Polynomial.C (Polynomial.X ^ p - Polynomial.C c)
  have hrel : e (MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
      MvPolynomial.C c) = g := by
    dsimp [g]
    simp only [map_add, map_sub, map_pow, hX0, hX1, hC]
    ring
  have hprime : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_X_sq_sub_C_X_pow_sub_C p K c hp)
  have hmap : Ideal.map (e : B →+* Polynomial R)
      (Ideal.span {MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
        MvPolynomial.C c}) = Ideal.span {g} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    show Ideal.span {e (MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
      MvPolynomial.C c)} = _
    rw [hrel]
  have hEqI : Ideal.comap (e : B →+* Polynomial R) (Ideal.span {g}) =
      Ideal.span {MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
        MvPolynomial.C c} := by
    rw [← hmap]
    exact Ideal.comap_map_of_bijective (e : B →+* Polynomial R) e.bijective
  rw [Ideal.Quotient.isDomain_iff_prime, ← hEqI]
  exact ((Ideal.span_singleton_prime hprime.ne_zero).mpr hprime).comap (e : B →+* Polynomial R)

private theorem curveRing_isDomain (hp : 2 < p) : IsDomain (curveRing p) :=
  baseChangedEquation_isDomain p (RatFunc (ZMod p)) RatFunc.X hp

private noncomputable def curveRing_baseChangeEquiv (L : Type*) [Field L]
    [Algebra (RatFunc (ZMod p)) L] :
    (L ⊗[RatFunc (ZMod p)] curveRing p) ≃+*
      (MvPolynomial (Fin 2) L ⧸ Ideal.span
        {MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
          MvPolynomial.C (algebraMap (RatFunc (ZMod p)) L RatFunc.X)}) := by
  let k := RatFunc (ZMod p)
  let B := MvPolynomial (Fin 2) k
  let I : Ideal B := Ideal.span {curveEquation p}
  let B' := MvPolynomial (Fin 2) L
  let f' : B' := MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
    MvPolynomial.C (algebraMap k L RatFunc.X)
  let e₁ : B ⊗[k] L ≃+* B' :=
    (Algebra.TensorProduct.comm k B L).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k L).toRingEquiv
  have heI : Ideal.map e₁ (Ideal.map (algebraMap B (B ⊗[k] L)) I) = Ideal.span {f'} := by
    rw [Ideal.map_span, Ideal.map_span]
    simp only [Set.image_singleton]
    have he₁ (b : B) : e₁ (algebraMap B (B ⊗[k] L) b) = MvPolynomial.map (algebraMap k L) b := by
      change MvPolynomial.algebraTensorAlgEquiv k L (1 ⊗ₜ[k] b) = _
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
      simp
    rw [show e₁ (algebraMap B (B ⊗[k] L) (curveEquation p)) = f' by
      simp [curveEquation, f', he₁]]
  exact (Algebra.TensorProduct.comm k L (B ⧸ I)).toRingEquiv.trans <|
    (Algebra.TensorProduct.quotientTensorEquiv (R := k) (S := k) (T := L)
      (A := B) I).toRingEquiv.trans (Ideal.quotientEquiv _ _ e₁ heI.symm)

private theorem curveRing_tensor_adjoinPthRoots_isReduced (hp : 2 < p) :
    _root_.IsReduced (AdjoinPthRoots (RatFunc (ZMod p)) ⊗[RatFunc (ZMod p)] curveRing p) := by
  let L := AdjoinPthRoots (RatFunc (ZMod p))
  have := baseChangedEquation_isDomain p L
    (algebraMap (RatFunc (ZMod p)) L RatFunc.X) hp
  let e := curveRing_baseChangeEquiv p L
  exact isReduced_of_injective e e.injective

/-- **Stacks Project, Tag 038Y.** The curve is a variety over `𝔽ₚ(t)`. -/
@[stacks 038Y "geometrically_reduced_not_geometrically_normal",
  ega "IV 6.7.5" "(i) X integral curve"]
theorem curve_isVariety (hp : 2 < p) :
    IsVariety (RatFunc (ZMod p)) (curveToBase p) := by
  have : IsDomain (curveRing p) := curveRing_isDomain p hp
  have : Algebra.FiniteType (RatFunc (ZMod p)) (curveRing p) := inferInstance
  have : LocallyOfFiniteType (curveToBase p) := by
    show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap (RatFunc (ZMod p)) (curveRing p))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    simpa [RingHom.finiteType_algebraMap]
  have : IsAffineHom (curveToBase p) := inferInstance
  exact {}

/-- **Stacks Project, Tag 038Y.** The curve is regular. -/
@[stacks 038Y "geometrically_reduced_not_geometrically_normal", ega "IV 6.7.5" "(i) X regular"]
theorem curve_isRegular (_hp : 2 < p) :
    IsRegular (curve p) := by
  have hreg : IsRegularRing (curveRing p) := curveRing_isRegularRing p
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, by simp, ?_⟩
  let e : Γ(curve p, ⊤) ≃+* curveRing p :=
    (Scheme.ΓSpecIso (.of (curveRing p))).commRingCatIsoToRingEquiv
  exact IsRegularRing.of_ringEquiv e.symm

/-- **Stacks Project, Tag 038Y.** The curve is geometrically reduced. -/
@[stacks 038Y "geometrically_reduced_not_geometrically_normal",
  ega "IV 6.7.5" "(i) X geom. integral"]
theorem curve_geometricallyReduced (hp : 2 < p) :
    GeometricallyReduced (curveToBase p) := by
  let k := RatFunc (ZMod p)
  let kperf := PerfectClosure k p
  let : Algebra k kperf := (PerfectClosure.of k p).toAlgebra
  let : IsPerfectClosure (algebraMap k kperf) p := PerfectClosure.isPRadical k p
  let tfae := geometricallyReduced_tfae k p (curveToBase p) kperf (AlgebraicClosure k)
  apply (tfae.out 1 4).mpr
  show IsReduced (Limits.pullback (curveToBase p)
    (Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinPthRoots k)))))
  let : Algebra k (AdjoinPthRoots k) := inferInstance
  have hr : _root_.IsReduced (AdjoinPthRoots k ⊗[k] curveRing p) :=
    curveRing_tensor_adjoinPthRoots_isReduced p hp
  have hr' : _root_.IsReduced (curveRing p ⊗[k] AdjoinPthRoots k) := by
    let e := (Algebra.TensorProduct.comm k (curveRing p) (AdjoinPthRoots k)).toRingEquiv
    exact isReduced_of_injective e e.injective
  exact CategoryTheory.ObjectProperty.prop_of_iso IsReduced
    (pullbackSpecIso k (curveRing p) (AdjoinPthRoots k)).symm ((affine_isReduced_iff _).2 hr')

private theorem local_integrallyClosed_of_normal (R : Type*) [CommRing R] [IsLocalRing R]
    (h : IsNormalRing R) : IsIntegrallyClosed R := by
  let m := IsLocalRing.maximalIdeal R
  have hi : IsIntegrallyClosed (Localization.AtPrime m) := (h m).2
  let e : R ≃+* Localization.AtPrime m :=
    (IsLocalization.atUnits R m.primeCompl (S := Localization.AtPrime m)
      fun _ => IsLocalRing.notMem_maximalIdeal.mp).toRingEquiv
  exact IsIntegrallyClosed.of_equiv e.symm

private theorem affine_integrallyClosed_of_stalks (A : Type*) [CommRing A] [IsDomain A]
    (h : ∀ x : Spec (.of A), IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x)) :
    IsIntegrallyClosed A := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let x : PrimeSpectrum A := ⟨P, inferInstance⟩
  have : IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x) := h x
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv

private theorem cusp_not_integrallyClosed (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (c : K) (hp : 2 < p)
    [IsDomain (MvPolynomial (Fin 2) K ⧸ Ideal.span
      {MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
        MvPolynomial.C (c ^ p)})] :
    ¬ IsIntegrallyClosed (MvPolynomial (Fin 2) K ⧸ Ideal.span
      {MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
        MvPolynomial.C (c ^ p)}) := by
  let B := MvPolynomial (Fin 2) K
  let f : B := MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
    MvPolynomial.C (c ^ p)
  let I : Ideal B := Ideal.span {f}
  let A := B ⧸ I
  let q : B →+* A := Ideal.Quotient.mk I
  have : CharP A p := charP_of_injective_algebraMap (algebraMap K A).injective p
  let x := q (MvPolynomial.X (0 : Fin 2)) - q (MvPolynomial.C c)
  let y := q (MvPolynomial.X (1 : Fin 2))
  have hf : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hrel : y ^ 2 = x ^ p := by
    dsimp [x, y]
    rw [sub_pow_char]
    dsimp [f] at hf
    simp only [map_add, map_sub, map_pow] at hf
    linear_combination hf
  intro hn
  let : IsIntegrallyClosed A := hn
  have hdiv : x ∣ y := (IsIntegrallyClosed.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp (by
    rw [hrel]
    exact pow_dvd_pow x (by omega : 2 ≤ p))
  let ev : B →+* DualNumber K := MvPolynomial.eval₂Hom
    (algebraMap K (DualNumber K)) (fun i => if i = 0 then algebraMap K (DualNumber K) c
      else DualNumber.eps)
  have hevX (i : Fin 2) : ev (MvPolynomial.X i) =
      (if i = 0 then algebraMap K (DualNumber K) c else DualNumber.eps) :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have hevC (a : K) : ev (MvPolynomial.C a) = algebraMap K (DualNumber K) a :=
    MvPolynomial.eval₂Hom_C _ _ _
  have hev : ev f = 0 := by
    dsimp only [f]
    rw [map_add, map_sub, map_pow, map_pow, hevX, hevX, hevC]
    simp
  let g : A →+* DualNumber K := Ideal.Quotient.lift I ev
    (by
      show I ≤ RingHom.ker ev
      apply Ideal.span_le.mpr
      rintro a (rfl : a = f)
      exact hev)
  have hx : g x = 0 := by
    dsimp [x]
    rw [map_sub]
    show ev (MvPolynomial.X (0 : Fin 2)) - ev (MvPolynomial.C c) = 0
    rw [hevX, hevC]
    simp
  have hy : g y = DualNumber.eps := by
    show ev (MvPolynomial.X (1 : Fin 2)) = _
    rw [hevX]
    simp
  obtain ⟨z, hz⟩ := hdiv
  have heps : (DualNumber.eps : DualNumber K) = 0 := by
    simpa [map_mul, hx, hy] using congrArg g hz
  simpa using congrArg TrivSqZeroExt.snd heps

/-- **Stacks Project, Tag 038Y.** The curve is not geometrically normal. -/
@[stacks 038Y "geometrically_reduced_not_geometrically_normal"]
theorem curve_not_isGeometricallyNormal (hp : 2 < p) :
    ¬ IsGeometricallyNormal (curveToBase p) := by
  intro hn
  let k := RatFunc (ZMod p)
  let L := AdjoinPthRoots k
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  let c : L := AdjoinPthRoots.root k RatFunc.X
  have hc : c ^ p = algebraMap k L RatFunc.X := AdjoinPthRoots.root_pow p RatFunc.X
  let Q := MvPolynomial (Fin 2) L ⧸ Ideal.span
    {MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X (0 : Fin 2) ^ p +
      MvPolynomial.C (algebraMap k L RatFunc.X)}
  have : IsDomain Q := baseChangedEquation_isDomain p L (algebraMap k L RatFunc.X) hp
  let A := curveRing p ⊗[k] L
  let e : A ≃+* Q := (Algebra.TensorProduct.comm k (curveRing p) L).toRingEquiv.trans
    (curveRing_baseChangeEquiv p L)
  have : IsDomain A := e.isDomain_iff.mpr inferInstance
  have : IsIntegrallyClosed A := by
    apply affine_integrallyClosed_of_stalks
    intro x
    let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let P : Scheme := Limits.pullback (curveToBase p) g
    let i : Spec (.of A) ⟶ P := (pullbackSpecIso k (curveRing p) L).inv
    have : IsIso i := inferInstanceAs (IsIso (pullbackSpecIso k (curveRing p) L).inv)
    have hnormal : IsNormalRing (P.presheaf.stalk (i x)) :=
      hn ((Limits.pullback.fst (curveToBase p) g) (i x)) L (i x) rfl
    have : IsLocalRing (P.presheaf.stalk (i x)) := P.toLocallyRingedSpace.isLocalRing _
    have : IsIntegrallyClosed (P.presheaf.stalk (i x)) :=
      local_integrallyClosed_of_normal (P.presheaf.stalk (i x)) hnormal
    exact IsIntegrallyClosed.of_equiv (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
  have hdomain := baseChangedEquation_isDomain p L (c ^ p) hp
  refine cusp_not_integrallyClosed p L c hp ?_
  rw [hc]
  exact IsIntegrallyClosed.of_equiv (R := A) (S := Q) e

end AlgebraicGeometry

end
