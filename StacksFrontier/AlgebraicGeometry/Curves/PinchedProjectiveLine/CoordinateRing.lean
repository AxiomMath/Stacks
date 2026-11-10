module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine

/-!
# The coordinate ring of the pinched affine line

Let `K/k` be a finite extension of fields. The subring of `K[X]` consisting of the polynomials
whose value at zero lies in `k` is the coordinate ring of the affine line over `K` with its
origin pinched down to a `k`-rational point. This file develops that ring and the two affine
charts of the pinched curve which are visible on it: the normalization chart
`Spec K[X] ⟶ Spec A`, which is finite and surjective, and the punctured chart
`Spec K[T, T⁻¹] ⟶ Spec A`, which is the open immersion complementary to the pinched point.

## Main definitions

* `AlgebraicGeometry.pinchedPolynomialRing` is the coordinate ring `A ⊆ K[X]`.
* `AlgebraicGeometry.pinchedPolynomialConstant` is its structure map from `k`.
* `AlgebraicGeometry.pinchedX` is the coordinate `X`, viewed in `A`.
* `AlgebraicGeometry.pinchedToLaurent` is the inclusion of `A` into `K[T, T⁻¹]`.
* `AlgebraicGeometry.pinchedPuncturedChart` is the punctured affine chart.
* `AlgebraicGeometry.pinchedNormalizationAffineChart` is the affine part of the normalization
  map.
* `AlgebraicGeometry.pinchedOrigin` is the pinched point of `Spec A`.

## Main results

* `AlgebraicGeometry.isLocalization_away_pinchedX` identifies `K[T, T⁻¹]` with the localization
  of `A` away from `X`, whence `pinchedPuncturedChart` is an open immersion.
* `AlgebraicGeometry.pinchedPuncturedChart_range` says that its image is the complement of the
  pinched point.
* `AlgebraicGeometry.not_isIntegrallyClosed_pinchedPolynomialRing`: for a nontrivial extension
  the coordinate ring is not integrally closed, so the pinched point is singular.
* `AlgebraicGeometry.topologicalKrullDim_spec_pinchedPolynomialRing` computes the dimension
  of the affine model as `1`.

## Implementation notes

The ring is defined as the inverse image under evaluation at zero of the image of `k` in `K`.
Its `k`-algebra structure is the one induced by the constant polynomials, and it is registered
as an instance together with the scalar tower `k → A → K[X]`; finiteness of `K[X]` over `A`
then follows from integrality and finite generation. The distinguished element `X` of `A` is
not a zero divisor and inverting it produces all of `K[T, T⁻¹]`, because multiplying a Laurent
polynomial's numerator by `X` always lands it in `A`.

## References

* [Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The coordinate ring of the pinched affine line: the polynomials over `K` whose value at
zero lies in the image of `k`.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
def pinchedPolynomialRing : Subring (Polynomial K) :=
  (algebraMap k K).range.comap (Polynomial.evalRingHom (0 : K))

/-- The constant-polynomial structure map from `k` into the pinched coordinate ring.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
def pinchedPolynomialConstant : k →+* pinchedPolynomialRing k K where
  toFun a := ⟨Polynomial.C (algebraMap k K a), by
    change Polynomial.evalRingHom (0 : K) (Polynomial.C (algebraMap k K a)) ∈
      (algebraMap k K).range
    exact ⟨a, by simp⟩⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- The coordinate `X` of the affine line, viewed as an element of the pinched coordinate ring.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
def pinchedX : pinchedPolynomialRing k K :=
  ⟨Polynomial.X, by
    change Polynomial.evalRingHom (0 : K) Polynomial.X ∈ (algebraMap k K).range
    exact ⟨0, by simp⟩⟩

/-- The `k`-algebra structure on the pinched coordinate ring, by constant polynomials. -/
instance pinchedPolynomialRing.instAlgebra : Algebra k (pinchedPolynomialRing k K) :=
  (pinchedPolynomialConstant k K).toAlgebra

/-- The pinched coordinate ring sits between `k` and `K[X]` as a tower of algebras.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
instance pinchedPolynomialRing.instIsScalarTower :
    IsScalarTower k (pinchedPolynomialRing k K) (Polynomial K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Every polynomial over `K` is integral over the pinched coordinate ring: the coordinate `X`
lies in that ring, and the constants are integral because `K/k` is finite. -/
theorem isIntegral_pinchedPolynomialRing [Module.Finite k K] (p : Polynomial K) :
    _root_.IsIntegral (pinchedPolynomialRing k K) p := by
  have hC : ∀ c : K, _root_.IsIntegral (pinchedPolynomialRing k K) (Polynomial.C c) :=
    fun c => ((IsIntegral.of_finite k c).algebraMap (B := Polynomial K)).tower_top
  have hX : _root_.IsIntegral (pinchedPolynomialRing k K) (Polynomial.X : Polynomial K) :=
    isIntegral_algebraMap (x := pinchedX k K)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact hp.add hq
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    exact (hC c).mul (hX.pow n)

/-- `K[X]` is integral over the pinched coordinate ring when `K/k` is finite.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
instance pinchedPolynomialRing.instIsIntegral [Module.Finite k K] :
    Algebra.IsIntegral (pinchedPolynomialRing k K) (Polynomial K) :=
  ⟨isIntegral_pinchedPolynomialRing k K⟩

/-- `K[X]` is a finite module over the pinched coordinate ring when `K/k` is finite: it is
integral over it and of finite type over it.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
instance pinchedPolynomialRing.instModuleFinite [Module.Finite k K] :
    Module.Finite (pinchedPolynomialRing k K) (Polynomial K) := by
  have : Algebra.FiniteType (pinchedPolynomialRing k K) (Polynomial K) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  exact Algebra.IsIntegral.finite

/-- The pinched coordinate ring is a finite-type `k`-algebra when `K/k` is finite.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
instance pinchedPolynomialRing.instFiniteType [Module.Finite k K] :
    Algebra.FiniteType k (pinchedPolynomialRing k K) :=
  ⟨fg_of_fg_of_fg k (pinchedPolynomialRing k K) (Polynomial K)
    Algebra.FiniteType.out Module.Finite.fg_top Subtype.val_injective⟩

/-- The pinched coordinate ring is Noetherian when `K/k` is finite.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
instance pinchedPolynomialRing.instIsNoetherianRing [Module.Finite k K] :
    IsNoetherianRing (pinchedPolynomialRing k K) :=
  Algebra.FiniteType.isNoetherianRing k _

/-- A polynomial over `K` vanishing at zero lies in the pinched coordinate ring. -/
private theorem mem_pinchedPolynomialRing_of_eval_zero {p : Polynomial K}
    (h : p.eval 0 = 0) : p ∈ pinchedPolynomialRing k K :=
  ⟨0, by simp [h]⟩

/-- Multiplication by `X` carries every polynomial over `K` into the pinched coordinate
ring. -/
private def pinchedMulX (p : Polynomial K) : pinchedPolynomialRing k K :=
  ⟨Polynomial.X * p, mem_pinchedPolynomialRing_of_eval_zero k K (by simp)⟩

/-- The pinched coordinate ring has the same fraction field as `K[X]`: every fraction can be
rewritten with numerator and denominator divisible by `X`. -/
instance pinchedPolynomialRing.instIsFractionRing :
    IsFractionRing (pinchedPolynomialRing k K) (FractionRing (Polynomial K)) := by
  have hi : Function.Injective
      (algebraMap (pinchedPolynomialRing k K) (FractionRing (Polynomial K))) :=
    (IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))).comp
      Subtype.val_injective
  have : FaithfulSMul (pinchedPolynomialRing k K) (FractionRing (Polynomial K)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hi
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (Polynomial K) z
  refine ⟨pinchedMulX k K p, pinchedMulX k K q, ?_⟩
  change algebraMap (Polynomial K) (FractionRing (Polynomial K)) p /
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) q =
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) (Polynomial.X * p) /
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) (Polynomial.X * q)
  rw [map_mul, map_mul, mul_div_mul_left]
  simpa only [map_zero] using
    (IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))).ne
      Polynomial.X_ne_zero

/-- For a nontrivial finite extension `K/k` the pinched coordinate ring is not integrally
closed: the constants of `K` are integral over it but only those of `k` belong to it.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
theorem not_isIntegrallyClosed_pinchedPolynomialRing [Module.Finite k K]
    (hK : 1 < Module.finrank k K) : ¬ IsIntegrallyClosed (pinchedPolynomialRing k K) := by
  intro hnormal
  let := hnormal
  apply hK.ne'
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨(algebraMap k K).injective, fun c => ?_⟩
  have hc := (isIntegral_pinchedPolynomialRing k K (Polynomial.C c)).algebraMap
    (B := FractionRing (Polynomial K))
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc
  have ha' : a.val = Polynomial.C c :=
    IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K)) ha
  have hm := a.property
  change Polynomial.evalRingHom (0 : K) a.val ∈ (algebraMap k K).range at hm
  rw [ha'] at hm
  simpa using hm

/-- The inclusion of the pinched coordinate ring into the Laurent polynomials over `K`. -/
def pinchedToLaurent : pinchedPolynomialRing k K →+* LaurentPolynomial K :=
  (Polynomial.toLaurent (R := K)).comp (Subring.subtype (pinchedPolynomialRing k K))

/-- Every Laurent polynomial over `K` splits as an element of the pinched coordinate ring plus
a polynomial in `T⁻¹`: a monomial of nonnegative degree already lies in the pinched ring, and
one of negative degree is the inverse of a polynomial. -/
theorem exists_pinched_add_invert_eq (z : LaurentPolynomial K) :
    ∃ (a : pinchedPolynomialRing k K) (b : Polynomial K),
      z = Polynomial.toLaurent a.val + LaurentPolynomial.invert (Polynomial.toLaurent b) := by
  induction z using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, b, rfl⟩ := hp
    obtain ⟨c, d, rfl⟩ := hq
    refine ⟨a + c, b + d, ?_⟩
    simp only [Subring.coe_add, map_add]
    abel
  | C_mul_T n c =>
    by_cases hn : 0 < n
    · have hpos : 0 < n.toNat := by omega
      have hnat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
      refine ⟨⟨Polynomial.monomial n.toNat c, mem_pinchedPolynomialRing_of_eval_zero k K
        (by simp [Polynomial.eval_monomial, Nat.ne_of_gt hpos])⟩, 0, ?_⟩
      simp [Polynomial.toLaurent_C_mul_T, hnat]
    · have hnat : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      refine ⟨0, Polynomial.monomial (-n).toNat c, ?_⟩
      simp [Polynomial.toLaurent_C_mul_T, hnat]

/-- Inverting the coordinate `X` on the pinched affine model recovers the punctured affine line
over `K`: every Laurent polynomial becomes the image of an element of the pinched ring after
multiplying its numerator by a power of `X`. -/
theorem isLocalization_away_pinchedX :
    letI : Algebra (pinchedPolynomialRing k K) (LaurentPolynomial K) :=
      (pinchedToLaurent k K).toAlgebra
    IsLocalization.Away (pinchedX k K) (LaurentPolynomial K) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨t, ⟨n, rfl⟩⟩
    change IsUnit (Polynomial.toLaurent (Polynomial.X ^ n : Polynomial K))
    rw [Polynomial.toLaurent_X_pow]
    exact LaurentPolynomial.isUnit_T n
  · intro z
    obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow z
    refine ⟨(pinchedMulX k K p, ⟨pinchedX k K ^ (n + 1), ⟨n + 1, rfl⟩⟩), ?_⟩
    change z * (pinchedToLaurent k K) (pinchedX k K ^ (n + 1)) = (pinchedToLaurent k K) _
    simp only [map_pow, pinchedToLaurent, RingHom.coe_comp, Function.comp_apply,
      Subring.coe_subtype, pinchedX, pinchedMulX]
    rw [map_mul, Polynomial.toLaurent_X, hp]
    simp only [LaurentPolynomial.T_pow, mul_one]
    rw [Nat.cast_add, Nat.cast_one, add_comm (n : ℤ) 1, LaurentPolynomial.T_add]
    ring
  · intro a b hab
    change Polynomial.toLaurent a.val = Polynomial.toLaurent b.val at hab
    obtain rfl : a = b := Subtype.ext (Polynomial.toLaurent_injective hab)
    exact ⟨1, by simp⟩

/-- The punctured chart of the pinched affine line, `Spec K[T, T⁻¹] ⟶ Spec A`.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
def pinchedPuncturedChart :
    Spec (.of (LaurentPolynomial K)) ⟶ Spec (.of (pinchedPolynomialRing k K)) :=
  Spec.map (CommRingCat.ofHom (pinchedToLaurent k K))

/-- The affine part of the normalization map, `Spec K[X] ⟶ Spec A`, induced by the inclusion
`A ⊆ K[X]`.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
def pinchedNormalizationAffineChart :
    Spec (.of (Polynomial K)) ⟶ Spec (.of (pinchedPolynomialRing k K)) :=
  Spec.map (CommRingCat.ofHom (Subring.subtype (pinchedPolynomialRing k K)))

/-- The punctured chart is an open immersion, being the spectrum of a localization of the
pinched coordinate ring away from the coordinate `X`.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
instance isOpenImmersion_pinchedPuncturedChart :
    IsOpenImmersion (pinchedPuncturedChart k K) := by
  let : Algebra (pinchedPolynomialRing k K) (LaurentPolynomial K) :=
    (pinchedToLaurent k K).toAlgebra
  have : IsLocalization.Away (pinchedX k K) (LaurentPolynomial K) :=
    isLocalization_away_pinchedX k K
  exact IsOpenImmersion.of_isLocalization (pinchedX k K)

/-- The affine normalization chart is a finite morphism when `K/k` is finite.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
instance isFinite_pinchedNormalizationAffineChart [Module.Finite k K] :
    IsFinite (pinchedNormalizationAffineChart k K) := by
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap (pinchedPolynomialRing k K) (Polynomial K))))
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The affine normalization chart is surjective: an integral extension with injective
structure map induces a surjection on spectra.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
instance surjective_pinchedNormalizationAffineChart [Module.Finite k K] :
    Surjective (pinchedNormalizationAffineChart k K) :=
  ⟨RingHom.IsIntegral.comap_surjective
    ((RingHom.finite_algebraMap.mpr (pinchedPolynomialRing.instModuleFinite k K)).to_isIntegral)
    Subtype.val_injective⟩

/-- The punctured chart factors the projective line's punctured chart through the normalization
chart: both are induced by `A ⊆ K[X] ⊆ K[T, T⁻¹]`. -/
theorem projectiveLinePuncturedChart_comp_pinchedNormalizationAffineChart :
    projectiveLinePuncturedChart K ≫ pinchedNormalizationAffineChart k K =
      pinchedPuncturedChart k K := by
  simp only [projectiveLinePuncturedChart, pinchedNormalizationAffineChart,
    pinchedPuncturedChart, ← Spec.map_comp]
  rfl

/-- The pinched point of `Spec A`: the image of the origin of the affine line over `K`.

[Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC) -/
def pinchedOrigin : Spec (.of (pinchedPolynomialRing k K)) :=
  PrimeSpectrum.comap (Subring.subtype (pinchedPolynomialRing k K)) (affineLineOrigin K)

/-- The pinched point is cut out by the contraction of the ideal `(X)` of `K[X]`. -/
theorem pinchedOrigin_asIdeal :
    (pinchedOrigin k K).asIdeal = (Ideal.span {(Polynomial.X : Polynomial K)}).comap
      (Subring.subtype (pinchedPolynomialRing k K)) := rfl

/-- The pinched point is a closed point, being the contraction of a maximal ideal along an
integral extension. -/
theorem isMaximal_pinchedOrigin [Module.Finite k K] :
    (pinchedOrigin k K).asIdeal.IsMaximal := by
  have : (Ideal.span {(Polynomial.X : Polynomial K)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  change ((Ideal.span {(Polynomial.X : Polynomial K)}).under
    (pinchedPolynomialRing k K)).IsMaximal
  infer_instance

/-- The coordinate `X` lies in exactly one prime of the pinched coordinate ring, the pinched
point: any prime containing it contains the contraction of `(X)`, because `a ^ 2 ∈ (X)` for
every `a` there. -/
private theorem pinchedX_mem_iff [Module.Finite k K]
    (q : PrimeSpectrum (pinchedPolynomialRing k K)) :
    pinchedX k K ∈ q.asIdeal ↔ q = pinchedOrigin k K := by
  refine ⟨fun hq => ?_, ?_⟩
  · refine PrimeSpectrum.ext ((isMaximal_pinchedOrigin k K).eq_of_le q.isPrime.ne_top
      fun a ha => ?_).symm
    change a.val ∈ Ideal.span {(Polynomial.X : Polynomial K)} at ha
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp ha
    have hpow : a ^ 2 = pinchedX k K * pinchedMulX k K (p ^ 2) := by
      apply Subtype.ext
      change a.val ^ 2 = Polynomial.X * (Polynomial.X * p ^ 2)
      rw [hp]
      ring
    exact q.isPrime.mem_of_pow_mem 2 (hpow ▸ q.asIdeal.mul_mem_right _ hq)
  · rintro rfl
    change Polynomial.X ∈ Ideal.span {(Polynomial.X : Polynomial K)}
    exact Ideal.mem_span_singleton_self _

/-- The punctured chart is the complement of the pinched point. -/
theorem pinchedPuncturedChart_range [Module.Finite k K] :
    Set.range (pinchedPuncturedChart k K) = {pinchedOrigin k K}ᶜ := by
  let : Algebra (pinchedPolynomialRing k K) (LaurentPolynomial K) :=
    (pinchedToLaurent k K).toAlgebra
  have := isLocalization_away_pinchedX k K
  change Set.range (PrimeSpectrum.comap
    (algebraMap (pinchedPolynomialRing k K) (LaurentPolynomial K))) = _
  rw [PrimeSpectrum.localization_away_comap_range _ (pinchedX k K)]
  ext q
  exact not_congr (pinchedX_mem_iff k K q)

/-- The affine line over a field has Krull dimension one: the Krull dimension of a spectrum is
the Krull dimension of the ring, and `dim K[X] = dim K + 1 = 1`. -/
theorem topologicalKrullDim_spec_polynomial :
    topologicalKrullDim (Spec (.of (Polynomial K))) = 1 := by
  change topologicalKrullDim (PrimeSpectrum (Polynomial K)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  rfl

/-- The pinched affine model has dimension one, since it is the target of a finite surjective
map from the affine line. -/
theorem topologicalKrullDim_spec_pinchedPolynomialRing [Module.Finite k K] :
    topologicalKrullDim (Spec (.of (pinchedPolynomialRing k K))) = 1 :=
  (topologicalKrullDim_eq_of_isIntegralHom_of_surjective
    (pinchedNormalizationAffineChart k K)).symm.trans (topologicalKrullDim_spec_polynomial K)

end AlgebraicGeometry

end
