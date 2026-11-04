module

public import StacksFrontier.AlgebraicGeometry.RelativeWeakNormalizationAway.Easy
public import StacksFrontier.AlgebraicGeometry.RelativeWeakNormalizationAway.SubalgebraAway
public import Mathlib.RingTheory.Localization.Integral

/-!
# Clearing denominators out of the relative weak normalization over a localized base

Let `A → B` be an algebra inducing a dominant morphism on spectra, let `r` be an element of `A`,
and let `Af` and `Bf` be the localizations away from `r`. This file proves the hard inclusion of
[Stacks, Tag 0H3K](https://stacks.math.columbia.edu/tag/0H3K): every element of the relative weak
normalization of `Af` in `Bf` is a fraction with a power of `r` as denominator and a numerator in
the relative weak normalization of `A` in `B`.

The source clears denominators inside the explicit tower of
[Stacks, Tag 0CNE](https://stacks.math.columbia.edu/tag/0CNE) using
[Stacks, Tag 0CN9](https://stacks.math.columbia.edu/tag/0CN9), after first reducing to the case of
reduced rings. The argument here uses neither, and needs no reduction step. Write `D` for the
relative weak normalization of `Af` in `Bf` and let `C₀` be the subalgebra of `B` of elements
that are integral over `A` and whose image lies in `D`. Every element of `D` is a fraction with
numerator in `C₀`, by clearing one denominator and then making the numerator integral. The
subalgebra `C₁` generated over `A` by `r · C₀` is then already universally homeomorphic over `A`,
hence contained in the relative weak normalization of `A` in `B`, and `C₀` becomes contained in
the relative weak normalization after inverting `r`.

The one step with content is that the spectrum of `C₁` is universally injective over `A`, and the
multiplication by `r` is exactly what buys it. Two field-valued maps out of `C₁` agreeing on `A`
are compared by cases on whether `r` is sent to zero. If it is, then every generator `r * c` is
sent to zero by both, because its square is `r · (r * c²)`, a product of two elements of `C₁` one
of which is `r`. If it is not, then both maps extend to `D`, where they agree because `D` is
universally injective over `Af`; the extension exists because `D` is the localization of `C₁`
away from `r`, which is where `IsLocalization.Away.of_subalgebra` is used.

## Main definitions

* `AlgebraicGeometry.integralPreimage` is the subalgebra `C₀` above.

## Main results

* `AlgebraicGeometry.exists_pow_mul_mem_integralPreimage`: every element of a subalgebra of `Bf`
  that is integral over `Af` is a fraction with numerator in `C₀`.
* `AlgebraicGeometry.mul_mem_relativeWeakNormalization`: `r` times an element of `C₀` lies in the
  relative weak normalization of `A` in `B`.
* `AlgebraicGeometry.exists_pow_mul_mem_relativeWeakNormalization`: the hard inclusion of
  Stacks 0H3K.

## References

* [Stacks Project, Tag 0H3K](https://stacks.math.columbia.edu/tag/0H3K)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {A B Af Bf : Type u} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bf]
  [Algebra A B] [Algebra A Af] [Algebra Af Bf] [Algebra A Bf] [Algebra B Bf]
  [IsScalarTower A B Bf] [IsScalarTower A Af Bf]

variable (A) in
/-- The subalgebra of `B` of elements integral over `A` whose image in a localization `Bf` lies
in a given subalgebra `D`. -/
def integralPreimage (D : Subalgebra Af Bf) : Subalgebra A B :=
  Subalgebra.comap (IsScalarTower.toAlgHom A B Bf) (D.restrictScalars A) ⊓ integralClosure A B

/-- An element `b` of `B` lies in `AlgebraicGeometry.integralPreimage A D` if and only if its
image in `Bf` lies in `D` and `b` is integral over `A`. -/
@[simp]
theorem mem_integralPreimage {D : Subalgebra Af Bf} {b : B} :
    b ∈ integralPreimage A D ↔ algebraMap B Bf b ∈ D ∧ _root_.IsIntegral A b :=
  Iff.rfl

/-- Multiplying a fraction `x / r ^ n = c` by `r ^ k` on both sides gives the fraction
`x / r ^ (n + k) = r ^ k * c`. -/
private theorem mul_pow_add_eq_algebraMap_mul (r : A) {x : Bf} {c : B} {n : ℕ}
    (k : ℕ) (h : x * algebraMap A Bf r ^ n = algebraMap B Bf c) :
    x * algebraMap A Bf r ^ (n + k) = algebraMap B Bf (algebraMap A B r ^ k * c) := by
  rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply A B Bf, pow_add, ← h]
  ring

/-- Every element of a subalgebra of `Bf` that is integral over `Af` is a fraction with a power
of `r` as denominator and a numerator in `AlgebraicGeometry.integralPreimage`. -/
theorem exists_pow_mul_mem_integralPreimage (r : A) [IsLocalization.Away r Af]
    [IsLocalization.Away (algebraMap A B r) Bf] (D : Subalgebra Af Bf)
    [Algebra.IsIntegral Af D] (d : D) :
    ∃ (n : ℕ) (c : B), c ∈ integralPreimage A D ∧
      (d : Bf) * algebraMap A Bf r ^ n = algebraMap B Bf c := by
  obtain ⟨⟨b, y⟩, hy⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A B r)) (d : Bf)
  obtain ⟨m, hm⟩ := y.2
  have hym : (y : B) = algebraMap A B r ^ m := hm.symm
  have hy' : (d : Bf) * algebraMap A Bf r ^ m = algebraMap B Bf b := by
    rw [IsScalarTower.algebraMap_apply A B Bf, ← map_pow, ← hym]
    exact hy
  have hrD : algebraMap A Bf r ∈ D := by
    rw [IsScalarTower.algebraMap_apply A Af Bf]
    exact D.algebraMap_mem _
  have hbD : algebraMap B Bf b ∈ D := by
    rw [← hy']
    exact D.mul_mem d.2 (D.pow_mem hrD m)
  have hintBf : _root_.IsIntegral Af (algebraMap B Bf b) :=
    (‹Algebra.IsIntegral Af D›.isIntegral (⟨_, hbD⟩ : D)).map D.val
  obtain ⟨u, hu⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (M := Submonoid.powers r) (Rₘ := Af) (algebraMap B Bf b) hintBf
  obtain ⟨p, hp⟩ := u.2
  have hup : (u : A) = r ^ p := hp.symm
  have hu' : _root_.IsIntegral A (algebraMap B Bf (algebraMap A B r ^ p * b)) := by
    have hre : algebraMap B Bf (algebraMap A B r ^ p * b) = (u : A) • algebraMap B Bf b := by
      simp [Algebra.smul_def, hup, IsScalarTower.algebraMap_apply A B Bf]
    rw [hre]
    exact hu
  obtain ⟨q, hq⟩ := IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap
    (R := A) (S := B) (Sₘ := Bf) (r := algebraMap A B r) (isIntegral_algebraMap) hu'
  refine ⟨m + (q + p), algebraMap A B r ^ (q + p) * b, mem_integralPreimage.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply A B Bf]
    exact D.mul_mem (D.pow_mem hrD _) hbD
  · rw [show algebraMap A B r ^ (q + p) * b
        = algebraMap A B r ^ q * (algebraMap A B r ^ p * b) by rw [← mul_assoc, ← pow_add]]
    exact hq
  · exact mul_pow_add_eq_algebraMap_mul r _ hy'

/-- Multiplication by `r` carries `AlgebraicGeometry.integralPreimage` into the relative weak
normalization of `A` in `B`, provided the ambient subalgebra of `Bf` has universally homeomorphic
spectrum over `Af` and every one of its elements is a fraction with numerator in that
preimage. -/
theorem mul_mem_relativeWeakNormalization (r : A) [IsLocalization.Away r Af]
    [IsLocalization.Away (algebraMap A B r) Bf]
    (hker : RingHom.ker (algebraMap A B) ≤ nilradical A) (C₀ : Subalgebra A B)
    (hCint : ∀ c ∈ C₀, _root_.IsIntegral A c) (D : Subalgebra Af Bf)
    (hD : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Af D)).op))
    (hCD : ∀ c ∈ C₀, algebraMap B Bf c ∈ D)
    (hfrac : ∀ d : D, ∃ (n : ℕ) (c : B), c ∈ C₀ ∧
      (d : Bf) * algebraMap A Bf r ^ n = algebraMap B Bf c)
    {c : B} (hc : c ∈ C₀) :
    algebraMap A B r * c ∈ relativeWeakNormalization A B := by
  set s : Set B := (fun y => algebraMap A B r * y) '' (C₀ : Set B) with hs
  have hsmem : ∀ y ∈ C₀, algebraMap A B r * y ∈ s := fun y hy => ⟨y, hy, rfl⟩
  have hsC₀ : ∀ x ∈ s, x ∈ C₀ := by
    rintro x ⟨y, hy, rfl⟩
    exact C₀.mul_mem (C₀.algebraMap_mem r) hy
  have hC₁C₀ : Algebra.adjoin A s ≤ C₀ := Algebra.adjoin_le hsC₀
  have hintC₁ : Algebra.IsIntegral A (Algebra.adjoin A s) :=
    Algebra.IsIntegral.adjoin fun x hx => hCint x (hsC₀ x hx)
  have hC₁D : ∀ x ∈ Algebra.adjoin A s, algebraMap B Bf x ∈ D :=
    fun x hx => hCD x (hC₁C₀ hx)
  let jhom : Algebra.adjoin A s →+* D :=
    { toFun := fun x => ⟨algebraMap B Bf (x : B), hC₁D _ x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  let _ : Algebra (Algebra.adjoin A s) D := jhom.toAlgebra
  have hjm : ∀ x : Algebra.adjoin A s,
      ((algebraMap (Algebra.adjoin A s) D x : D) : Bf) = algebraMap B Bf (x : B) :=
    fun _ => rfl
  have halg : ∀ a : A, algebraMap (Algebra.adjoin A s) D (algebraMap A (Algebra.adjoin A s) a) =
      algebraMap Af D (algebraMap A Af a) := by
    intro a
    apply Subtype.ext
    rw [hjm, show ((algebraMap A (Algebra.adjoin A s) a : Algebra.adjoin A s) : B)
        = algebraMap A B a from rfl, ← IsScalarTower.algebraMap_apply A B Bf,
      IsScalarTower.algebraMap_apply A Af Bf]
    rfl
  have hunit : IsUnit (algebraMap (Algebra.adjoin A s) D
      (algebraMap A (Algebra.adjoin A s) r)) := by
    rw [halg]
    exact (IsLocalization.map_units Af
      (⟨r, Submonoid.mem_powers r⟩ : Submonoid.powers r)).map (algebraMap Af D)
  have hloc : IsLocalization.Away (algebraMap A (Algebra.adjoin A s) r) D := by
    refine IsLocalization.Away.of_subalgebra r (Algebra.adjoin A s) D D.val.toRingHom
      (fun x y h => Subtype.ext h) hjm hunit fun d => ?_
    obtain ⟨n, y, hy, hd⟩ := hfrac d
    refine ⟨n + 1, ⟨algebraMap A B r * y, Algebra.subset_adjoin (hsmem y hy)⟩, ?_⟩
    simpa using mul_pow_add_eq_algebraMap_mul r 1 hd
  have huniq : ∀ (K : Type u) [Field K] (φ ψ : Algebra.adjoin A s →+* K),
      φ.comp (algebraMap A (Algebra.adjoin A s)) =
        ψ.comp (algebraMap A (Algebra.adjoin A s)) → φ = ψ := by
    intro K _ φ ψ hcomp
    have hbase : ∀ a : A, φ (algebraMap A (Algebra.adjoin A s) a) =
        ψ (algebraMap A (Algebra.adjoin A s) a) :=
      fun a => congrArg (fun q : A →+* K => q a) hcomp
    by_cases hr0 : φ (algebraMap A (Algebra.adjoin A s) r) = 0
    · apply RingHom.ext
      rintro ⟨w, hw⟩
      induction hw using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        have hsq : ∀ h : algebraMap A B r * y ∈ Algebra.adjoin A s,
            (⟨algebraMap A B r * y, h⟩ : Algebra.adjoin A s) ^ 2 =
              algebraMap A (Algebra.adjoin A s) r *
                ⟨algebraMap A B r * (y * y),
                  Algebra.subset_adjoin (hsmem _ (C₀.mul_mem hy hy))⟩ := by
          intro h
          apply Subtype.ext
          push_cast
          ring
        have hzero : ∀ (χ : Algebra.adjoin A s →+* K),
            χ (algebraMap A (Algebra.adjoin A s) r) = 0 →
            ∀ h : algebraMap A B r * y ∈ Algebra.adjoin A s,
              χ ⟨algebraMap A B r * y, h⟩ = 0 := by
          intro χ hχ h
          have h2 := congrArg χ (hsq h)
          rw [map_pow, map_mul, hχ, zero_mul] at h2
          exact sq_eq_zero_iff.mp h2
        rw [hzero φ hr0, hzero ψ ((hbase r).symm.trans hr0)]
      | algebraMap a => exact hbase a
      | add x y hx hy ihx ihy =>
        have e : ∀ h : x + y ∈ Algebra.adjoin A s,
            (⟨x + y, h⟩ : Algebra.adjoin A s) = ⟨x, hx⟩ + ⟨y, hy⟩ := fun _ => Subtype.ext rfl
        rw [e, map_add, map_add, ihx, ihy]
      | mul x y hx hy ihx ihy =>
        have e : ∀ h : x * y ∈ Algebra.adjoin A s,
            (⟨x * y, h⟩ : Algebra.adjoin A s) = ⟨x, hx⟩ * ⟨y, hy⟩ := fun _ => Subtype.ext rfl
        rw [e, map_mul, map_mul, ihx, ihy]
    · have hψ0 : ψ (algebraMap A (Algebra.adjoin A s) r) ≠ 0 :=
        fun h => hr0 ((hbase r).trans h)
      have hunits : ∀ (χ : Algebra.adjoin A s →+* K),
          χ (algebraMap A (Algebra.adjoin A s) r) ≠ 0 →
          ∀ y : Submonoid.powers (algebraMap A (Algebra.adjoin A s) r), IsUnit (χ y) := by
        rintro χ hχ ⟨-, n, rfl⟩
        rw [map_pow]
        exact hχ.isUnit.pow n
      have huφ := hunits φ hr0
      have huψ := hunits ψ hψ0
      have hΦ : (IsLocalization.lift huφ).comp (algebraMap (Algebra.adjoin A s) D) = φ :=
        IsLocalization.lift_comp huφ
      have hΨ : (IsLocalization.lift huψ).comp (algebraMap (Algebra.adjoin A s) D) = ψ :=
        IsLocalization.lift_comp huψ
      have hAf : ∀ a : Af, IsLocalization.lift huφ (algebraMap Af D a) =
          IsLocalization.lift huψ (algebraMap Af D a) := by
        have key : ((IsLocalization.lift huφ).comp (algebraMap Af D)).comp (algebraMap A Af) =
            ((IsLocalization.lift huψ).comp (algebraMap Af D)).comp (algebraMap A Af) := by
          apply RingHom.ext
          intro a
          simp only [RingHom.comp_apply, ← halg]
          rw [IsLocalization.lift_eq, IsLocalization.lift_eq]
          exact hbase a
        exact fun a => congrArg (fun q : Af →+* K => q a)
          (IsLocalization.ringHom_ext (Submonoid.powers r) key)
      rw [← hΦ, ← hΨ, ringHom_eq_of_universalHomeomorphism (algebraMap Af D) hD _ _ hAf]
  have hC₁ : UniversalHomeomorphism (Scheme.Spec.map
      (CommRingCat.ofHom (algebraMap A (Algebra.adjoin A s))).op) :=
    universalHomeomorphism_specMap_of_isIntegral
      (ker_algebraMap_subalgebra_le_nilradical _ hker) huniq
  have hle := range_le_relativeWeakNormalization A B (Algebra.adjoin A s)
    (Algebra.adjoin A s).val (isDominant_specMap_iff_ker_le_nilradical.mpr hker) hC₁
  rw [Subalgebra.range_val] at hle
  exact hle (Algebra.subset_adjoin (hsmem c hc))

/-- Every element of the relative weak normalization over a localized base is a fraction with a
power of `r` as denominator and a numerator in the relative weak normalization. This is the hard
inclusion of Stacks 0H3K. -/
theorem exists_pow_mul_mem_relativeWeakNormalization (r : A) [IsLocalization.Away r Af]
    [IsLocalization.Away (algebraMap A B r) Bf]
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (d : relativeWeakNormalization Af Bf) :
    ∃ (n : ℕ) (b : relativeWeakNormalization A B),
      (d : Bf) * algebraMap A Bf r ^ n = algebraMap B Bf (b : B) := by
  have hker := isDominant_specMap_iff_ker_le_nilradical.mp hdom
  have hdomf : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Af Bf)).op) :=
    isDominant_specMap_iff_ker_le_nilradical.mpr
      (ker_algebraMap_localization_le_nilradical (B := B) r hker)
  have hD := relativeWeakNormalization_isUniversalHomeomorphism Af Bf hdomf
  have hintD : Algebra.IsIntegral Af (relativeWeakNormalization Af Bf) :=
    algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp
      ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp hD).1)
  obtain ⟨n, c, hc, hd⟩ :=
    exists_pow_mul_mem_integralPreimage (A := A) (B := B) r (relativeWeakNormalization Af Bf) d
  have hmul : algebraMap A B r * c ∈ relativeWeakNormalization A B :=
    mul_mem_relativeWeakNormalization r hker _
      (fun x hx => (mem_integralPreimage.mp hx).2) (relativeWeakNormalization Af Bf) hD
      (fun x hx => (mem_integralPreimage.mp hx).1)
      (fun e => exists_pow_mul_mem_integralPreimage (A := A) (B := B) r
        (relativeWeakNormalization Af Bf) e) hc
  refine ⟨n + 1, ⟨algebraMap A B r * c, hmul⟩, ?_⟩
  simpa using mul_pow_add_eq_algebraMap_mul r 1 hd

end AlgebraicGeometry

end
