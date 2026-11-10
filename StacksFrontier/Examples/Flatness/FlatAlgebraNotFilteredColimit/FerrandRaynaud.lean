module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Basic.Countable.Defs
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Set.Countable
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.OfPrime
public import Mathlib.RingTheory.Trace.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.Examples.Flatness.FlatAlgebraNotFilteredColimit.ColimitObstruction
public import StacksFrontier.Examples.Flatness.FlatAlgebraNotFilteredColimit.RingOfConstants

/-!
# The Ferrand–Raynaud ring of constants

Let `D : ℚ[[X]] → ℚ((X))` be a `ℚ`-derivation with `D X = 0` and `D s = X⁻¹` for a power series
`s` with zero constant term, let `E` be `D` followed by the quotient map
`ℚ((X)) → ℚ((X)) ⧸ ℚ[[X]]`, and let `A = {f : E f = 0}` be its ring of constants. Then `A` is a
Henselian Noetherian local ring of dimension one containing `ℚ` whose `X`-adic completion is not
reduced, so that this completion is a flat `A`-algebra which is the colimit of no filtered
diagram of finitely presented flat `A`-algebras.

## References

* [Stacks Project, Tag 0ATF](https://stacks.math.columbia.edu/tag/0ATF)
* D. Ferrand and M. Raynaud, *Fibres formelles d'un anneau local noethérien*,
  Ann. Sci. Éc. Norm. Supér. 3 (1970), 295–311, Proposition 3.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Examples.FlatAlgebraNotFilteredColimit

open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin
open scoped RatFunc LaurentSeries

/-- The universe lift of the rational numbers has characteristic zero. -/
local instance : CharZero (ULift.{u} ℚ) :=
  ULift.ringEquiv.toRingHom.charZero

/-- Scalars from the rationals act on the Laurent series through the power series. -/
local instance : IsScalarTower (ULift.{u} ℚ)
    (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) := by
  refine ⟨fun r b z => ?_⟩
  change (r.down • b) • z = r.down • (b • z)
  simp [Algebra.smul_def, map_mul, PowerSeries.algebraMap_apply,
    Rat.smul_def, mul_assoc]

/-- A derivation extends along a formally étale map. -/
private alias exists_derivation_extension_of_formallyEtale :=
  RingHom.exists_derivation_of_formallyEtale

/-- Values on a transcendence basis determine a derivation in characteristic zero. -/
private lemma exists_derivation_of_isTranscendenceBasis
    {R K ι : Type*} [Field R] [Field K] [Algebra R K] [CharZero R]
    {x : ι → K} (hx : IsTranscendenceBasis R x) (f : ι → K) :
    ∃ D : Derivation R K K, ∀ i, D (x i) = f i := by
  let A := Algebra.adjoin R (Set.range x)
  let B := IntermediateField.adjoin R (Set.range x)
  let e : MvPolynomial ι R ≃ₐ[R] A := hx.1.aevalEquiv
  let : Algebra (MvPolynomial ι R) K := (MvPolynomial.aeval x).toAlgebra
  let DP : Derivation R (MvPolynomial ι R) K := MvPolynomial.mkDerivation R f
  have he (a : A) : (MvPolynomial.aeval x) (e.symm a) = (a : K) := by
    rw [← hx.1.algebraMap_aevalEquiv]
    exact congrArg (fun a : A => (a : K)) (e.apply_symm_apply a)
  let DA : Derivation R A K :=
    { DP.toLinearMap.comp e.symm.toLinearMap with
      map_one_eq_zero' := by simp
      leibniz' := by
        intro a b
        change DP (e.symm (a * b)) = a • DP (e.symm b) + b • DP (e.symm a)
        rw [map_mul, DP.leibniz]
        change (MvPolynomial.aeval x) (e.symm a) * DP (e.symm b) +
            (MvPolynomial.aeval x) (e.symm b) * DP (e.symm a) = _
        rw [he, he]
        rfl }
  have : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  obtain ⟨DB, hDB⟩ := exists_derivation_extension_of_formallyEtale (B := B) DA
  have : Algebra.IsAlgebraic B K := hx.isAlgebraic_field
  have : Algebra.FormallyEtale B K := Algebra.FormallyEtale.of_isSeparable B K
  obtain ⟨DK, hDK⟩ := exists_derivation_extension_of_formallyEtale (B := K) DB
  refine ⟨DK, fun i => ?_⟩
  have hxA : (e (MvPolynomial.X i) : K) = x i :=
    (hx.1.algebraMap_aevalEquiv (MvPolynomial.X i)).trans (MvPolynomial.aeval_X x i)
  rw [← hxA]
  change DK (algebraMap A K (e (MvPolynomial.X i))) = _
  rw [IsScalarTower.algebraMap_apply A B K, hDK, hDB]
  change DP (e.symm (e (MvPolynomial.X i))) = _
  rw [e.symm_apply_apply]
  exact MvPolynomial.mkDerivation_X R f i

/-- A transcendental extension in characteristic zero admits a nonzero derivation. -/
private lemma exists_nonzero_derivation_of_transcendental
    (R K : Type*) [Field R] [Field K] [Algebra R K] [CharZero R]
    (h : ¬ Algebra.IsAlgebraic R K) : ∃ D : Derivation R K K, ∃ x : K, D x = 1 := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' R K
  have hι : Nonempty ι := not_isEmpty_iff.mp (fun hi => h (hx.isEmpty_iff_isAlgebraic.mp hi))
  obtain ⟨D, hD⟩ := exists_derivation_of_isTranscendenceBasis hx (fun _ => 1)
  obtain ⟨i⟩ := hι
  exact ⟨D, x i, hD i⟩

/-- Laurent series over the rationals admit a nonzero derivation over rational functions. -/
private lemma exists_derivation_laurentSeries_rat :
    ∃ D : Derivation (RatFunc (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)),
      ∃ x : LaurentSeries (ULift.{u} ℚ), D x = 1 := by
  apply exists_nonzero_derivation_of_transcendental
  intro h
  have : Countable (AddMonoidAlgebra (ULift.{u} ℚ) ℕ) :=
    Function.Injective.countable AddMonoidAlgebra.coeff_injective
  have : Countable (Polynomial (ULift.{u} ℚ)) :=
    Function.Injective.countable Polynomial.toFinsupp_injective
  have : Countable (RatFunc (ULift.{u} ℚ)) := Function.Surjective.countable
    (f := fun pq : Polynomial (ULift.{u} ℚ) × Polynomial (ULift.{u} ℚ) => RatFunc.mk pq.1 pq.2) (by
      intro z
      exact ⟨(z.num, z.denom), by exact (RatFunc.mk_eq_div _ _).trans (RatFunc.num_div_denom z)⟩)
  have hcount : Countable (LaurentSeries (ULift.{u} ℚ)) := by
    apply Cardinal.mk_le_aleph0_iff.mp
    have hle := Algebra.IsAlgebraic.cardinalMk_le_max (RatFunc (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ))
    have hrat : Cardinal.mk (RatFunc (ULift.{u} ℚ)) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
    simpa only [max_eq_right hrat] using hle
  have hinj : Function.Injective (fun f : ℕ → (ULift.{u} ℚ) =>
      (algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
        (PowerSeries.mk f)) := by
    intro f g hfg
    have hmk := (FaithfulSMul.algebraMap_injective (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ))) hfg
    funext n
    simpa only [PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff n) hmk
  have : Countable (ℕ → (ULift.{u} ℚ)) := Function.Injective.countable hinj
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ → (ULift.{u} ℚ))
  obtain ⟨n, hn⟩ := he (fun n => e n n + 1)
  have hnn := congrFun hn n
  exact one_ne_zero (add_left_cancel (a := e n n) (by simpa using hnn.symm))

/-- There is a derivation on rational power series which kills the uniformizer and
takes a power series with zero constant coefficient to the inverse uniformizer. -/
private lemma exists_derivation_powerSeries_rat :
    ∃ D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)),
      D PowerSeries.X = 0 ∧ ∃ s : PowerSeries (ULift.{u} ℚ),
        PowerSeries.constantCoeff s = 0 ∧
          D s = (algebraMap (PowerSeries (ULift.{u} ℚ))
            (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹ := by
  obtain ⟨E, x, hx⟩ := exists_derivation_laurentSeries_rat
  let D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) :=
    { toLinearMap :=
        { toFun := fun b =>
            E (algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) b)
          map_add' := by intro a b; simp only [map_add]
          map_smul' := by
            intro r b
            change E ((algebraMap (PowerSeries (ULift.{u} ℚ))
              (LaurentSeries (ULift.{u} ℚ))) (r.down • b)) =
              r.down • E ((algebraMap (PowerSeries (ULift.{u} ℚ))
                (LaurentSeries (ULift.{u} ℚ))) b)
            simp only [map_rat_smul] }
      map_one_eq_zero' := by
        change E (algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) 1) = 0
        rw [map_one, E.map_one_eq_zero]
      leibniz' := by
        intro a b
        change E (algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) (a * b)) =
          a • E (algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) b) +
          b • E (algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) a)
        simp only [map_mul, E.leibniz, smul_eq_mul, Algebra.smul_def] }
  have hDX : D PowerSeries.X = 0 := by
    change
      E (algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X) = 0
    rw [show algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X =
      algebraMap (RatFunc (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) RatFunc.X by
        rw [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X, RatFunc.coe_X]]
    exact E.map_algebraMap _
  obtain ⟨⟨f, t⟩, hft⟩ := IsLocalization.surj
    (Submonoid.powers (PowerSeries.X : PowerSeries (ULift.{u} ℚ))) x
  obtain ⟨n, hn⟩ := t.property
  have hfn : E (algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) f) =
      algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X ^ n := by
    have h := congrArg E hft
    simp only [← hn, map_pow, E.leibniz, hx, smul_eq_mul, mul_one] at h
    have ht0 : E (algebraMap (PowerSeries (ULift.{u} ℚ))
        (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X ^ n) = 0 := by
      rw [E.leibniz_pow]
      change n • _ • D PowerSeries.X = 0
      rw [hDX, smul_zero, smul_zero]
    rw [ht0, mul_zero, zero_add] at h
    exact h.symm
  let q : LaurentSeries (ULift.{u} ℚ) :=
    algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X
  have hq : q ≠ 0 := fun h => PowerSeries.X_ne_zero (R := (ULift.{u} ℚ))
    (FaithfulSMul.algebraMap_injective (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ))
      (h.trans (map_zero _).symm))
  let s : PowerSeries (ULift.{u} ℚ) := f - PowerSeries.C (PowerSeries.constantCoeff f)
  have hDs : D s = q ^ n := by
    have hDC : D (PowerSeries.C (PowerSeries.constantCoeff f)) = 0 := D.map_algebraMap _
    dsimp [s]
    rwa [map_sub, hDC, sub_zero]
  refine ⟨(q⁻¹ * (q ^ n)⁻¹) • D, ?_, s, ?_, ?_⟩
  · simp only [Derivation.smul_apply, hDX, smul_zero]
  · simp [s]
  · simp only [Derivation.smul_apply, hDs, smul_eq_mul]
    change (q⁻¹ * (q ^ n)⁻¹) * q ^ n = q⁻¹
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hq), mul_one]

/-- The quotient of a principal localization by the base ring is power torsion. -/
private lemma exists_pow_smul_eq_zero_quotient_range
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (t : R) [IsLocalization.Away t S]
    (m : S ⧸ (Algebra.linearMap R S).range) : ∃ n : ℕ, t ^ n • m = 0 := by
  induction m using Submodule.Quotient.induction_on with
  | _ x =>
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (Submonoid.powers t) x
    obtain ⟨n, hn⟩ := b.property
    refine ⟨n, ?_⟩
    change (Algebra.linearMap R S).range.mkQ (t ^ n • x) = 0
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    refine ⟨a, ?_⟩
    simpa only [Algebra.linearMap_apply, Algebra.smul_def, hn, mul_comm] using hab.symm

/-- The image of the power-series variable in the Laurent series is nonzero. -/
private lemma algebraMap_powerSeries_X_ne_zero (k : Type*) [Field k] :
    algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr PowerSeries.X_ne_zero

/-- Every power series is a constant plus a multiple of the variable. -/
private lemma exists_powerSeries_sub_algebraMap_eq_X_mul {k : Type*} [Field k]
    (b : PowerSeries k) :
    ∃ (r : k) (c : PowerSeries k), b - algebraMap k (PowerSeries k) r = PowerSeries.X * c :=
  ⟨PowerSeries.constantCoeff b, PowerSeries.mk (fun n => PowerSeries.coeff (n + 1) b),
    PowerSeries.sub_const_eq_X_mul_shift b⟩

/-- The `X`-torsion in `k((X))/k[[X]]` is generated by the class of `X⁻¹`. -/
private lemma quotient_powerSeries_X_torsion
    {k : Type*} [Field k]
    (m : LaurentSeries k ⧸ (Algebra.linearMap (PowerSeries k) (LaurentSeries k)).range)
    (hm : (PowerSeries.X : PowerSeries k) • m = 0) :
    ∃ r : k, m = (PowerSeries.C r : PowerSeries k) •
      ((Algebra.linearMap (PowerSeries k) (LaurentSeries k)).range.mkQ
        ((algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X)⁻¹)) := by
  let B := PowerSeries k
  let L := LaurentSeries k
  let N : Submodule B L := (Algebra.linearMap B L).range
  let qx : L := algebraMap B L PowerSeries.X
  change ∃ r : k, m = (PowerSeries.C r : B) • N.mkQ qx⁻¹
  induction m using Submodule.Quotient.induction_on with
  | _ v =>
    have hXv : qx * v ∈ N := by
      have hz : N.mkQ ((PowerSeries.X : B) • v) = 0 := by simpa using hm
      have hmem : ((PowerSeries.X : B) • v) ∈ N :=
        (Submodule.Quotient.mk_eq_zero N).mp hz
      simpa only [Algebra.smul_def] using hmem
    obtain ⟨w, hw⟩ := hXv
    let r : k := PowerSeries.constantCoeff w
    let g : B := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) w
    have hsplit : w = PowerSeries.X * g + PowerSeries.C r :=
      PowerSeries.eq_X_mul_shift_add_const w
    have hqx : qx ≠ 0 := algebraMap_powerSeries_X_ne_zero k
    have hv : v = algebraMap B L g + algebraMap B L (PowerSeries.C r) * qx⁻¹ := by
      apply (mul_left_cancel₀ hqx)
      calc
        qx * v = algebraMap B L w := hw.symm
        _ = qx * (algebraMap B L g + algebraMap B L (PowerSeries.C r) * qx⁻¹) := by
          rw [hsplit, map_add, map_mul]
          dsimp [qx]
          calc
            qx * g + PowerSeries.C r =
                qx * g + PowerSeries.C r * (qx * qx⁻¹) := by
              rw [mul_inv_cancel₀ hqx, mul_one]
            _ = qx * (g + PowerSeries.C r * qx⁻¹) := by ring
    refine ⟨r, ?_⟩
    change N.mkQ v = (PowerSeries.C r : B) • N.mkQ qx⁻¹
    rw [hv, map_add]
    have hg : N.mkQ (algebraMap B L g) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr ⟨g, rfl⟩
    rw [hg, zero_add]
    change N.mkQ ((PowerSeries.C r) • qx⁻¹) =
      (PowerSeries.C r : B) • N.mkQ qx⁻¹
    rw [map_smul]

/-- The residue field of the constants of a rational derivation has characteristic zero. -/
private lemma charZero_residueField_derivationConstants
    {B M : Type*} [CommRing B] [IsLocalRing B] [AddCommGroup M]
    [Algebra (ULift.{u} ℚ) B] [Module B M] [Module (ULift.{u} ℚ) M]
    (D : Derivation (ULift.{u} ℚ) B M) :
    letI : IsLocalRing (derivationConstants D) := isLocalRing_derivationConstants D
    CharZero (IsLocalRing.ResidueField (derivationConstants D)) := by
  have : IsLocalRing (derivationConstants D) := isLocalRing_derivationConstants D
  exact Algebra.charZero_of_charZero (ULift.{u} ℚ) _

/-- An integral local subring of a one-dimensional domain has dimension one
when it contains a nonzero nonunit. -/
private lemma ringKrullDim_eq_one_of_integral_local_extension
    (A B : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Ring.KrullDimLE 1 B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (x : A) (hx0 : x ≠ 0) (hxunit : ¬ IsUnit x) :
    ringKrullDim A = 1 := by
  have : Ring.KrullDimLE 1 A := Ring.KrullDimLE.mk₁' (by
    intro I hI hI0
    obtain ⟨Q, hQ, hQI⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := B) I (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)]
        exact bot_le)
    have hQ0 : Q ≠ ⊥ := by
      intro heq
      apply hI
      rw [← hQI, heq]
      exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)
    have := hQ.isMaximal_of_ne_bot hQ0
    exact hQI ▸ (inferInstance : (Q.under A).IsMaximal))
  apply ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mpr
  constructor
  · intro hfield
    let : Field A := hfield.toField
    exact hxunit (isUnit_iff_ne_zero.mpr hx0)
  · intro y hy
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro P hP
    obtain ⟨hspan, hprime⟩ := hP
    have hP0 : P ≠ ⊥ := by
      intro heq
      have hmem : y ∈ P := hspan (Ideal.subset_span (Set.mem_singleton y))
      rw [heq] at hmem
      exact hy (by simpa using hmem)
    have hPmax : P.IsMaximal := hprime.isMaximal_of_ne_bot hP0
    exact le_of_eq (IsLocalRing.eq_maximalIdeal hPmax).symm

/-- Rational scalars act compatibly on the quotient of the Laurent series by the power series. -/
private lemma isScalarTower_powerSeries_quotient_range :
    IsScalarTower (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ))
      ((LaurentSeries (ULift.{u} ℚ)) ⧸
        (Algebra.linearMap (PowerSeries (ULift.{u} ℚ))
          (LaurentSeries (ULift.{u} ℚ))).range) := by
  let N : Submodule (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) :=
    (Algebra.linearMap _ _).range
  refine ⟨fun r b z => ?_⟩
  induction z using Submodule.Quotient.induction_on with | _ z =>
  change N.mkQ ((r.down • b) • z) = N.mkQ (r.down • (b • z))
  congr 1
  simp [Algebra.smul_def, map_mul, Rat.smul_def, mul_assoc]

/-- The pole class of a derivation of the power series: `D` composed with the quotient
of the Laurent series by the power series, so that it records only the polar part of
each derivative. -/
private noncomputable def poleClassDerivation
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ))) :
    Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ))
      ((LaurentSeries (ULift.{u} ℚ)) ⧸
        (Algebra.linearMap (PowerSeries (ULift.{u} ℚ))
          (LaurentSeries (ULift.{u} ℚ))).range) := by
  let B := PowerSeries (ULift.{u} ℚ)
  let L := LaurentSeries (ULift.{u} ℚ)
  let N : Submodule B L := (Algebra.linearMap B L).range
  have : IsScalarTower (ULift.{u} ℚ) B L := inferInstance
  exact (@Derivation.llcomp (ULift.{u} ℚ) B L _ _ _ _ _ _
    (L ⧸ N) _ _ _ this isScalarTower_powerSeries_quotient_range N.mkQ) D

/-- The pole class of the variable vanishes when the derivation kills the variable. -/
private lemma poleClassDerivation_X
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) : poleClassDerivation D PowerSeries.X = 0 := by
  let B := PowerSeries (ULift.{u} ℚ)
  let L := LaurentSeries (ULift.{u} ℚ)
  let N : Submodule B L := (Algebra.linearMap B L).range
  change N.mkQ (D PowerSeries.X) = 0
  rw [hDX, map_zero]

/-- The pole class of `X * y` vanishes when `D y` is the inverse uniformizer. -/
private lemma poleClassDerivation_X_mul
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (y : PowerSeries (ULift.{u} ℚ))
    (hy : D y = (algebraMap (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹) :
    poleClassDerivation D (PowerSeries.X * y) = 0 := by
  let B := PowerSeries (ULift.{u} ℚ)
  let L := LaurentSeries (ULift.{u} ℚ)
  let N : Submodule B L := (Algebra.linearMap B L).range
  change N.mkQ (D (PowerSeries.X * y)) = 0
  rw [D.leibniz, hDX, smul_zero, add_zero, hy, Algebra.smul_def]
  change N.mkQ (_ * _) = 0
  rw [mul_inv_cancel₀ (algebraMap_powerSeries_X_ne_zero _)]
  exact (Submodule.Quotient.mk_eq_zero N).mpr ⟨1, by simp⟩

/-- The variable is a nonunit among the constants of the pole-class derivation. -/
private lemma not_isUnit_uniformizer
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) :
    ¬ IsUnit (⟨PowerSeries.X, poleClassDerivation_X D hDX⟩ :
      derivationConstants (poleClassDerivation D)) := fun h => by
  have hX : PowerSeries.X ∈ IsLocalRing.maximalIdeal (PowerSeries (ULift.{u} ℚ)) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact hX ((isUnit_derivationConstants_iff _ _).mp h)

/-- The constants of the pole-class derivation on rational power series form a
Noetherian ring when one derivative is the inverse uniformizer. -/
private lemma isNoetherianRing_powerSeries_derivationConstants
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (s : PowerSeries (ULift.{u} ℚ))
    (hs : D s = (algebraMap (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹) :
    IsNoetherianRing
      (derivationConstants (poleClassDerivation D)) := by
  let B := PowerSeries (ULift.{u} ℚ)
  let L := LaurentSeries (ULift.{u} ℚ)
  let N : Submodule B L := (Algebra.linearMap B L).range
  let qx : L := algebraMap B L PowerSeries.X
  let E : Derivation (ULift.{u} ℚ) B (L ⧸ N) := poleClassDerivation D
  let t : derivationConstants E := ⟨PowerSeries.X, poleClassDerivation_X D hDX⟩
  let z : derivationConstants E := ⟨PowerSeries.X * s, poleClassDerivation_X_mul D hDX s hs⟩
  apply @isNoetherianRing_derivationConstants (ULift.{u} ℚ) B (L ⧸ N)
    _ _ _ _ _ _ _ _ _ isScalarTower_powerSeries_quotient_range E t z s
  · exact PowerSeries.maximalIdeal_eq_span_X
  · rfl
  · intro b hb
    obtain ⟨r, hr⟩ := quotient_powerSeries_X_torsion (E b) hb
    refine ⟨r, ?_⟩
    have hEs : E s = N.mkQ qx⁻¹ := by
      change N.mkQ (D s) = N.mkQ qx⁻¹
      rw [hs]
    rw [hr, hEs]
    change N.mkQ ((algebraMap (ULift.{u} ℚ) B r) • qx⁻¹) =
      N.mkQ (r.down • qx⁻¹)
    apply congrArg N.mkQ
    simp only [Algebra.smul_def, Rat.smul_def, mul_eq_mul_right_iff, inv_eq_zero]
    left
    change ((PowerSeries.C r : B) : L) = (r.down : L)
    rw [PowerSeries.coe_C]
    cases r
    rfl
  · exact exists_powerSeries_sub_algebraMap_eq_X_mul
  · exact fun m => exists_pow_smul_eq_zero_quotient_range PowerSeries.X m

/-- The derivation-constants construction has dimension one. -/
private lemma ringKrullDim_powerSeries_derivationConstants
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) :
    ringKrullDim
      (derivationConstants (poleClassDerivation D)) = 1 := by
  let B := PowerSeries (ULift.{u} ℚ)
  let L := LaurentSeries (ULift.{u} ℚ)
  let N : Submodule B L := (Algebra.linearMap B L).range
  let E : Derivation (ULift.{u} ℚ) B (L ⧸ N) := poleClassDerivation D
  let A := derivationConstants E
  have : IsLocalRing A := isLocalRing_derivationConstants E
  let t : A := ⟨PowerSeries.X, poleClassDerivation_X D hDX⟩
  have : Algebra.IsIntegral A B :=
    isIntegral_derivationConstants_of_uniformizer_torsion E t
      exists_powerSeries_sub_algebraMap_eq_X_mul
      (fun m => exists_pow_smul_eq_zero_quotient_range PowerSeries.X m)
  have ht0 : t ≠ 0 := fun h => PowerSeries.X_ne_zero (congrArg (fun x : A => (x : B)) h)
  exact ringKrullDim_eq_one_of_integral_local_extension A B t ht0
    (not_isUnit_uniformizer D hDX)

/-- A derivation annihilating the power-series variable annihilates each polynomial truncation. -/
private lemma derivation_trunc_zero
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (s : PowerSeries (ULift.{u} ℚ)) (n : ℕ) :
    D (↑(s.trunc n) : PowerSeries (ULift.{u} ℚ)) = 0 := by
  have hmap : algebraMap (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) = PowerSeries.C := by
    ext r
    simp
  have hcoe : Polynomial.aeval (PowerSeries.X : PowerSeries (ULift.{u} ℚ)) (s.trunc n) =
      (↑(s.trunc n) : PowerSeries (ULift.{u} ℚ)) := by
    rw [Polynomial.aeval_def, hmap]
    exact Polynomial.eval₂_C_X_eq_coe
  rw [← hcoe, D.map_aeval, hDX, smul_zero]

/-- Truncating the distinguished power series gives constants of the pole-class derivation. -/
private noncomputable def derivationConstants_approximant
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (s : PowerSeries (ULift.{u} ℚ))
    (hs : D s = (algebraMap (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹)
    (n : ℕ) :
    derivationConstants (poleClassDerivation D) := by
  let B := PowerSeries (ULift.{u} ℚ)
  let L := LaurentSeries (ULift.{u} ℚ)
  let N : Submodule B L := (Algebra.linearMap B L).range
  refine ⟨PowerSeries.X * (s - (s.trunc n : B)),
    poleClassDerivation_X_mul D hDX _ ?_⟩
  rw [map_sub, derivation_trunc_zero D hDX s n, sub_zero, hs]

/-- The inverse uniformizer has a genuine pole in the Laurent-series field. -/
private lemma powerSeries_X_inv_not_mem_range :
    (algebraMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹ ∉
      (Algebra.linearMap (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ))).range := by
  let B := PowerSeries (ULift.{u} ℚ)
  let L := LaurentSeries (ULift.{u} ℚ)
  let qx : L := algebraMap B L PowerSeries.X
  have hqx : qx ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B L)).mpr PowerSeries.X_ne_zero
  rintro ⟨b, hb⟩
  change algebraMap B L b = qx⁻¹ at hb
  have hmul : PowerSeries.X * b = (1 : B) := by
    apply FaithfulSMul.algebraMap_injective B L
    simp only [map_mul, map_one]
    change qx * algebraMap B L b = 1
    rw [hb]
    exact mul_inv_cancel₀ hqx
  have hcoeff := congrArg PowerSeries.constantCoeff hmul
  simp only [map_mul, PowerSeries.constantCoeff_X, zero_mul,
    map_one] at hcoeff
  exact zero_ne_one hcoeff

/-- No approximant is divisible by the square of the uniformizer inside the constants. -/
private lemma derivationConstants_approximant_ne_X_sq_mul
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (s : PowerSeries (ULift.{u} ℚ))
    (hs : D s = (algebraMap (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹)
    (n : ℕ)
    (b : derivationConstants (poleClassDerivation D)) :
    derivationConstants_approximant D hDX s hs n ≠
      (⟨PowerSeries.X, poleClassDerivation_X D hDX⟩ :
        derivationConstants (poleClassDerivation D)) ^ 2 * b := by
  let B := PowerSeries (ULift.{u} ℚ)
  let L := LaurentSeries (ULift.{u} ℚ)
  let N : Submodule B L := (Algebra.linearMap B L).range
  let E : Derivation (ULift.{u} ℚ) B (L ⧸ N) := poleClassDerivation D
  let t : derivationConstants E := ⟨PowerSeries.X, poleClassDerivation_X D hDX⟩
  intro heq
  have heqB : PowerSeries.X * (s - (s.trunc n : B)) =
      PowerSeries.X ^ 2 * (b : B) := congrArg (fun a : derivationConstants E => (a : B)) heq
  have hsplit : s - (s.trunc n : B) = PowerSeries.X * (b : B) := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := (ULift.{u} ℚ)))
    simpa only [pow_two, mul_assoc] using heqB
  have hE : E (s - (s.trunc n : B)) = N.mkQ
      ((algebraMap B L PowerSeries.X)⁻¹) := by
    change N.mkQ (D (s - (s.trunc n : B))) = _
    rw [map_sub, derivation_trunc_zero D hDX s n, sub_zero, hs]
  rw [hsplit, E.leibniz, show E PowerSeries.X = 0 from t.property,
    show E (b : B) = 0 from b.property] at hE
  simp only [smul_zero, zero_add] at hE
  exact powerSeries_X_inv_not_mem_range
    ((Submodule.Quotient.mk_eq_zero N).mp hE.symm)

/-- Consecutive approximants differ by the next power of the uniformizer. -/
private lemma derivationConstants_approximant_sub_succ
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (s : PowerSeries (ULift.{u} ℚ))
    (hs : D s = (algebraMap (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹)
    (n : ℕ) :
    derivationConstants_approximant D hDX s hs n -
      derivationConstants_approximant D hDX s hs (n + 1) =
      (⟨PowerSeries.X, poleClassDerivation_X D hDX⟩ :
        derivationConstants (poleClassDerivation D)) ^ (n + 1) *
        algebraMap (ULift.{u} ℚ) _ (PowerSeries.coeff n s) := by
  apply Subtype.ext
  change PowerSeries.X * (s - (s.trunc n : PowerSeries (ULift.{u} ℚ))) -
      PowerSeries.X * (s - (s.trunc (n + 1) : PowerSeries (ULift.{u} ℚ))) =
      PowerSeries.X ^ (n + 1) * PowerSeries.C (PowerSeries.coeff n s)
  rw [PowerSeries.trunc_succ, Polynomial.coe_add,
    ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  ring

/-- A constant divisible by `t ^ (n + 1)` in the ambient ring has square divisible
by `t ^ n` inside the constants. -/
private lemma derivationConstants_sq_mem_pow
    {R B M : Type*} [CommRing R] [CommRing B] [AddCommGroup M]
    [Algebra R B] [Module B M] [Module R M]
    (D : Derivation R B M) (t x : derivationConstants D) (n : ℕ) (u : B)
    (hx : (x : B) = (t : B) ^ (n + 1) * u) :
    x ^ 2 ∈ (Ideal.span {t} : Ideal (derivationConstants D)) ^ n := by
  have hDpow : D ((t : B) ^ (n + 1)) = 0 := by
    rw [D.leibniz_pow, t.property, smul_zero, smul_zero]
  have hDu : (t : B) ^ (n + 1) • D u = 0 := by
    have h : D (x : B) = 0 := x.property
    rw [hx, D.leibniz, hDpow, smul_zero, add_zero] at h
    exact h
  have hDtu : D ((t : B) * u) = (t : B) • D u := by
    rw [D.leibniz, t.property, smul_zero, add_zero]
  let y : derivationConstants D := ⟨(x : B) * ((t : B) * u), by
    change D ((x : B) * ((t : B) * u)) = 0
    rw [D.leibniz, x.property, smul_zero, add_zero, hDtu, hx]
    calc
      ((t : B) ^ (n + 1) * u) • ((t : B) • D u) =
          ((t : B) * u) • ((t : B) ^ (n + 1) • D u) := by
            repeat rw [smul_smul]
            congr 1
            ring
      _ = 0 := by rw [hDu, smul_zero]⟩
  have heq : x ^ 2 = t ^ n * y := by
    apply Subtype.ext
    change (x : B) ^ 2 = (t : B) ^ n * ((x : B) * ((t : B) * u))
    rw [hx]
    ring
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨y, heq⟩

/-- The square of each approximant vanishes to the required order inside the
constants ring. -/
private lemma derivationConstants_approximant_sq_mem_pow
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (s : PowerSeries (ULift.{u} ℚ))
    (hs : D s = (algebraMap (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹)
    (n : ℕ) :
    let E := poleClassDerivation D
    let A := derivationConstants E
    let t : A := ⟨PowerSeries.X, poleClassDerivation_X D hDX⟩
    (derivationConstants_approximant D hDX s hs n) ^ 2 ∈
      (Ideal.span {t} : Ideal A) ^ n := by
  intro E A t
  let u : PowerSeries (ULift.{u} ℚ) := PowerSeries.mk fun i => PowerSeries.coeff (i + n) s
  have hsplit : s - (s.trunc n : PowerSeries (ULift.{u} ℚ)) = PowerSeries.X ^ n * u :=
    sub_eq_iff_eq_add.mpr (PowerSeries.eq_X_pow_mul_shift_add_trunc n s)
  apply derivationConstants_sq_mem_pow E t
    (derivationConstants_approximant D hDX s hs n) n u
  change PowerSeries.X * (s - (s.trunc n : PowerSeries (ULift.{u} ℚ))) =
    PowerSeries.X ^ (n + 1) * u
  rw [hsplit]
  ring

/-- The distinguished approximants form a Cauchy sequence in the constants ring. -/
private noncomputable def derivationConstants_cauchySequence
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (s : PowerSeries (ULift.{u} ℚ))
    (hs : D s = (algebraMap (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹) :
    let E := poleClassDerivation D
    let A := derivationConstants E
    let t : A := ⟨PowerSeries.X, poleClassDerivation_X D hDX⟩
    AdicCompletion.AdicCauchySequence (Ideal.span {t}) A := by
  intro E A t
  apply AdicCompletion.AdicCauchySequence.mk (Ideal.span {t}) A
    (fun n => derivationConstants_approximant D hDX s hs n)
  intro n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨t * algebraMap (ULift.{u} ℚ) A (PowerSeries.coeff n s), ?_⟩
  rw [derivationConstants_approximant_sub_succ]
  ring

/-- The distinguished Cauchy sequence defines a nonzero point of the completion. -/
private lemma derivationConstants_completion_element_ne_zero
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (s : PowerSeries (ULift.{u} ℚ))
    (hs : D s = (algebraMap (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹) :
    let E := poleClassDerivation D
    let A := derivationConstants E
    let t : A := ⟨PowerSeries.X, poleClassDerivation_X D hDX⟩
    AdicCompletion.mkₐ (Ideal.span {t})
      (derivationConstants_cauchySequence D hDX s hs) ≠ 0 := by
  intro E A t hz
  have hq := congrArg (AdicCompletion.evalₐ (Ideal.span {t}) 2) hz
  rw [AdicCompletion.evalₐ_mkₐ, map_zero] at hq
  have ha : (derivationConstants_cauchySequence D hDX s hs) 2 ∈
      (Ideal.span {t} : Ideal A) ^ 2 := Ideal.Quotient.eq_zero_iff_mem.mp hq
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
  obtain ⟨b, hb⟩ := ha
  exact derivationConstants_approximant_ne_X_sq_mul D hDX s hs 2 b hb

/-- The constructed constants ring has a nonreduced uniformizer-adic completion. -/
private lemma derivationConstants_completion_not_reduced
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ)) (LaurentSeries (ULift.{u} ℚ)))
    (hDX : D PowerSeries.X = 0) (s : PowerSeries (ULift.{u} ℚ))
    (hs : D s = (algebraMap (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ)) PowerSeries.X)⁻¹) :
    let E := poleClassDerivation D
    let A := derivationConstants E
    let t : A := ⟨PowerSeries.X, poleClassDerivation_X D hDX⟩
    ¬ IsReduced (AdicCompletion (Ideal.span {t}) A) := by
  intro E A t hred
  let a := derivationConstants_cauchySequence D hDX s hs
  let x : AdicCompletion (Ideal.span {t}) A :=
    AdicCompletion.mkₐ (Ideal.span {t}) a
  have hx0 : x ≠ 0 := derivationConstants_completion_element_ne_zero D hDX s hs
  have hx2 : x ^ 2 = 0 := by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [map_pow, map_zero, show x = AdicCompletion.mkₐ (Ideal.span {t}) a from rfl,
      AdicCompletion.evalₐ_mkₐ, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (derivationConstants_approximant_sq_mem_pow D hDX s hs n)
  exact hx0 (hred.eq_zero x (IsNilpotent.mk x 2 hx2))

/-- The derivative of a polynomial with constant coefficients obeys the usual chain rule. -/
private lemma derivation_aeval_of_constants
    {R B M : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] [Module R M]
    (D : Derivation R B M) (P : Polynomial (derivationConstants D)) (x : B) :
    D (Polynomial.aeval x P) = Polynomial.aeval x P.derivative • D x := by
  let A := derivationConstants D
  let : Module A M := Module.compHom M (algebraMap A B)
  have hz : ((0 : Derivation R A M).mapCoeffs P) = 0 := by
    ext n
    simp
  have h := Derivation.apply_aeval_eq' (0 : Derivation R A M) D
    (LinearMap.id : M →ₗ[A] M) (by intro a; exact a.property.symm) x P
  simpa [hz] using h

/-- A Henselian ambient ring gives Henselian constants of a derivation. -/
private lemma henselianLocalRing_derivationConstants
    {R B M : Type*} [CommRing R] [CommRing B] [HenselianLocalRing B]
    [Algebra R B] [AddCommGroup M] [Module B M] [Module R M]
    (D : Derivation R B M) : HenselianLocalRing (derivationConstants D) := by
  let A := derivationConstants D
  have : IsLocalRing A := isLocalRing_derivationConstants D
  refine { is_henselian := ?_ }
  intro P hP a₀ hroot hunit
  let PB : Polynomial B := P.map (algebraMap A B)
  have heval (Q : Polynomial A) (x : A) :
      (Q.map (algebraMap A B)).eval (x : B) = ((Q.eval x : A) : B) :=
    Polynomial.eval_map_apply (algebraMap A B) x
  have hPBmonic : PB.Monic := hP.map (algebraMap A B)
  have hPBroot : PB.eval (a₀ : B) ∈ IsLocalRing.maximalIdeal B := by
    change ¬ IsUnit (PB.eval (a₀ : B))
    rw [show PB.eval (a₀ : B) = ((P.eval a₀ : A) : B) from heval P a₀]
    exact fun hu => hroot ((isUnit_derivationConstants_iff D (P.eval a₀)).mpr hu)
  have hPBunit : IsUnit (PB.derivative.eval (a₀ : B)) := by
    rw [show PB.derivative.eval (a₀ : B) = ((P.derivative.eval a₀ : A) : B) by
      simpa only [PB, Polynomial.derivative_map] using heval P.derivative a₀]
    exact hunit.map (algebraMap A B)
  obtain ⟨b, hbroot, hdiff⟩ :=
    HenselianLocalRing.is_henselian PB hPBmonic (a₀ : B) hPBroot hPBunit
  have hunitb : IsUnit (PB.derivative.eval b) := by
    apply IsUnit.of_map (IsLocalRing.residue B)
    have hmod : b ≡ (a₀ : B) [SMOD IsLocalRing.maximalIdeal B] :=
      SModEq.sub_mem.mpr hdiff
    rw [show (IsLocalRing.residue B) (PB.derivative.eval b) =
      (IsLocalRing.residue B) (PB.derivative.eval (a₀ : B)) from
        SModEq.def.mp (hmod.eval PB.derivative)]
    exact hPBunit.map (IsLocalRing.residue B)
  have hbzero : D b = 0 := by
    have hrootAe : Polynomial.aeval b P = 0 := by
      change PB.eval b = 0 at hbroot
      simpa only [PB, Polynomial.eval_map_algebraMap] using hbroot
    have hunitb' : IsUnit (Polynomial.aeval b P.derivative) := by
      simpa only [PB, Polynomial.derivative_map, Polynomial.eval_map_algebraMap] using hunitb
    have hchain := derivation_aeval_of_constants D P b
    rw [hrootAe, map_zero] at hchain
    exact (IsUnit.smul_eq_zero hunitb').mp hchain.symm
  let a : A := ⟨b, hbzero⟩
  refine ⟨a, ?_, ?_⟩
  · change P.eval a = 0
    apply Subtype.ext
    change PB.eval b = 0 at hbroot
    rwa [show PB.eval b = ((P.eval a : A) : B) from heval P a] at hbroot
  · change a - a₀ ∈ IsLocalRing.maximalIdeal A
    exact fun hu => hdiff ((isUnit_derivationConstants_iff D (a - a₀)).mp hu)

/-- The rational pole-class constants form a Henselian local ring. -/
private lemma henselianLocalRing_powerSeries_derivationConstants
    (D : Derivation (ULift.{u} ℚ) (PowerSeries (ULift.{u} ℚ))
      (LaurentSeries (ULift.{u} ℚ))) :
    HenselianLocalRing (derivationConstants (poleClassDerivation D)) := by
  let B := PowerSeries (ULift.{u} ℚ)
  have : IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have : HenselianLocalRing B := henselianLocalRing_of_isAdicComplete_maximalIdeal B
  exact henselianLocalRing_derivationConstants (poleClassDerivation D)

/-- There is a one-dimensional Noetherian local ring whose residue field has characteristic
zero carrying a flat algebra which is the colimit of no filtered diagram of finitely presented
flat algebras whose colimit the forgetful functor preserves. -/
lemma exists_charZero_local_example_of_preservesColimit :
    ∃ A : CommRingCat.{u}, ∃ hloc : IsLocalRing A,
      letI : IsLocalRing A := hloc
      IsNoetherianRing A ∧ ringKrullDim A = 1 ∧
        CharZero (IsLocalRing.ResidueField A) ∧
          ∃ B : CommAlgCat.{u} A, Module.Flat A B ∧
            ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
              (F : J ⥤ CommAlgCat.{u} A)
              [PreservesColimit F (forget (CommAlgCat.{u} A))],
              (∀ j, Algebra.FinitePresentation A (F.obj j) ∧
                Module.Flat A (F.obj j)) →
                ∀ c : Cocone F, c.pt = B → IsEmpty (IsColimit c) := by
  obtain ⟨D, hDX, s, _, hs⟩ := exists_derivation_powerSeries_rat.{u}
  let E := poleClassDerivation D
  let A := derivationConstants E
  have : IsLocalRing A := isLocalRing_derivationConstants E
  have : HenselianLocalRing A := henselianLocalRing_powerSeries_derivationConstants D
  have : IsNoetherianRing A := isNoetherianRing_powerSeries_derivationConstants D hDX s hs
  have : CharZero (IsLocalRing.ResidueField A) :=
    charZero_residueField_derivationConstants E
  let t : A := ⟨PowerSeries.X, poleClassDerivation_X D hDX⟩
  have htmax : t ∈ IsLocalRing.maximalIdeal A := not_isUnit_uniformizer D hDX
  have : Module.FaithfullyFlat A (AdicCompletion (Ideal.span {t}) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson (Ideal.span {t}) (by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact Ideal.span_le.mpr
        (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using htmax))
  have hred : IsReduced A := by infer_instance
  have hnot : ¬ IsReduced (AdicCompletion (Ideal.span {t}) A) :=
    derivationConstants_completion_not_reduced D hDX s hs
  refine ⟨CommRingCat.of A, isLocalRing_derivationConstants E,
    inferInstance, ringKrullDim_powerSeries_derivationConstants D hDX,
    charZero_residueField_derivationConstants E,
    CommAlgCat.of A (AdicCompletion (Ideal.span {t}) A), inferInstance, ?_⟩
  intro J _ _ F _ hF c hpt
  apply isEmpty_isColimit_of_not_isReduced_adicCompletion t hnot F c hpt
  intro i
  have : Module.Flat A (F.obj i) := (hF i).2
  have : Algebra.FinitePresentation A (F.obj i) := (hF i).1
  have : Module.FaithfullyFlat A (F.obj i) :=
    faithfullyFlat_stage_of_faithfullyFlat_cocone F c _ hpt i
  exact exists_finite_free_factor_of_faithfullyFlat_finitePresentation

end Stacks.Examples.FlatAlgebraNotFilteredColimit

end
