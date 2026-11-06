module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.MvPolynomial.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.RestrictedPowerSeriesMapBijective

/-!
# Restricted power series and principal localization of the coefficients

Let `I` be a finitely generated ideal of a commutative ring `A`, let `f : A` and let `A{σ}` be
the restricted power series ring for `I`.  Inverting the constant `f` in `A{σ}` and inverting `f`
in the coefficients give the same thing level by level: the localization of `A{σ}` away from `f`,
modulo the `n`-th power of the extended coefficient ideal, is the polynomial ring over
`A[1/f] ⧸ (I · A[1/f]) ^ n`.  Both commutations behind this are standard: a localization of a
quotient is the quotient of the localization, and a polynomial ring over a localization is a
localization of the polynomial ring.

Passing to the limit over `n`, the completion of `A{σ}[1/f]` along the extended coefficient ideal
is the restricted power series ring over `A[1/f]`; since restricted power series do not change
when the coefficient ring is completed, it is also the restricted power series ring over the
completed principal localization of `A` at `f`.

## Main definitions

* `TopologicalRing.awayRestrictedPowerSeriesMap`: the canonical map `A{σ}[1/f] → (A[1/f]){σ}`.
* `TopologicalRing.awayCoefficientIdeal`: the extension of the coefficient ideal to `A{σ}[1/f]`.
* `TopologicalRing.completedAwayRestrictedPowerSeriesMap`: the canonical map from the completion
  of `A{σ}[1/f]` to `(A[1/f]){σ}`, and `completedAwayRestrictedPowerSeriesInv` its inverse.

## Main results

* `TopologicalRing.surjective_awayCoefficientProjection` and
  `TopologicalRing.ker_awayCoefficientProjection`: the level `n` component of
  `A{σ}[1/f] → (A[1/f]){σ}` is surjective with kernel the `n`-th power of the extended
  coefficient ideal; `TopologicalRing.quotientAwayCoefficientIdealPowEquiv` is the resulting
  identification `A{σ}[1/f] ⧸ (I · A{σ}[1/f]) ^ n ≃+* (A[1/f] ⧸ (I · A[1/f]) ^ n)[σ]`.
* `TopologicalRing.bijective_completedAwayRestrictedPowerSeriesMap`: the completion of
  `A{σ}[1/f]` is `(A[1/f]){σ}`.
* `TopologicalRing.bijective_restrictedPowerSeriesMap_comp_completedAway`: the completed
  principal localization of `A{σ}` at `f` is the restricted power series ring over the completed
  principal localization of `A` at `f`.

## Implementation notes

The canonical map out of `A{σ}[1/f]` is obtained from `IsLocalization.Away.lift` applied to
`TopologicalRing.restrictedPowerSeriesMap`, whose value on the constant `f` is invertible because
`f` is invertible in `A[1/f]`; it is pinned down by its restriction to `A{σ}`.  The level `n`
identification is stated as surjectivity and a kernel computation for that canonical map rather
than by constructing an inverse, and the map out of the completion is pinned down by its level
`n` components.  Its inverse is assembled with `AdicCompletion.liftRingHom` from the inverses of
the level `n` identifications.

## References

* [Stacks Project, Tag 0AJM](https://stacks.math.columbia.edu/tag/0AJM)
* [Stacks Project, Tag 0GGG](https://stacks.math.columbia.edu/tag/0GGG)
-/

@[expose] public section

namespace TopologicalRing

section

universe u v

variable {A : Type u} [CommRing A]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The coefficient reduction `A ⧸ Iⁿ → A[1/f] ⧸ (I · A[1/f])ⁿ` as an algebra structure on the
target. -/
private noncomputable abbrev coefficientQuotientAwayAlgebra (I : Ideal A) (f : A) (n : ℕ) :
    Algebra (A ⧸ I ^ n)
      (Localization.Away f ⧸ (I.map (algebraMap A (Localization.Away f))) ^ n) :=
  (coefficientQuotientMap (B := Localization.Away f) I n).toAlgebra

attribute [local instance] coefficientQuotientAwayAlgebra

/-- Comparing the two descriptions of the extension of `Iⁿ` to the localization away from `f`. -/
private noncomputable def quotAwayPowEquiv (I : Ideal A) (f : A) (n : ℕ) :
    Localization.Away f ⧸ (I ^ n).map (algebraMap A (Localization.Away f)) ≃+*
      Localization.Away f ⧸ (I.map (algebraMap A (Localization.Away f))) ^ n :=
  Ideal.quotEquivOfEq (Ideal.map_pow (algebraMap A (Localization.Away f)) I n)

/-- The two descriptions of the extension of `Iⁿ` agree with the coefficient reduction. -/
private theorem quotAwayPowEquiv_comp_algebraMap (I : Ideal A) (f : A) (n : ℕ) :
    (quotAwayPowEquiv I f n).toRingHom.comp
        (algebraMap (A ⧸ I ^ n)
          (Localization.Away f ⧸ (I ^ n).map (algebraMap A (Localization.Away f)))) =
      coefficientQuotientMap (B := Localization.Away f) I n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

/-- **The polynomial ring over a principally localized coefficient quotient is a
localization.**  The polynomial ring over `A[1/f] ⧸ (I · A[1/f])ⁿ` is the localization of the
polynomial ring over `A ⧸ Iⁿ` away from the constant `f`. -/
private theorem isLocalization_mvPolynomial_coefficientQuotientAway (I : Ideal A) (f : A) (n : ℕ)
    (σ : Type v) :
    IsLocalization
      (Submonoid.powers
        (MvPolynomial.C (Ideal.Quotient.mk (I ^ n) f) : MvPolynomial σ (A ⧸ I ^ n)))
      (MvPolynomial σ
        (Localization.Away f ⧸ (I.map (algebraMap A (Localization.Away f))) ^ n)) := by
  have h0 : IsLocalization (Submonoid.powers (Ideal.Quotient.mk (I ^ n) f))
      (Localization.Away f ⧸ (I ^ n).map (algebraMap A (Localization.Away f))) := by
    have h := (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid (A ⧸ I ^ n) (Submonoid.powers f))
      (Localization.Away f ⧸ (I ^ n).map (algebraMap A (Localization.Away f))))
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h
  have h1 : IsLocalization
      (Submonoid.powers
        (MvPolynomial.C (Ideal.Quotient.mk (I ^ n) f) : MvPolynomial σ (A ⧸ I ^ n)))
      (MvPolynomial σ
        (Localization.Away f ⧸ (I ^ n).map (algebraMap A (Localization.Away f)))) := by
    have h := MvPolynomial.isLocalization (σ := σ)
      (Submonoid.powers (Ideal.Quotient.mk (I ^ n) f))
      (Localization.Away f ⧸ (I ^ n).map (algebraMap A (Localization.Away f)))
    rwa [Submonoid.map_powers] at h
  refine IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := MvPolynomial.mapEquiv σ (quotAwayPowEquiv I f n)) ?_)
  intro p
  show MvPolynomial.map (quotAwayPowEquiv I f n).toRingHom
      (MvPolynomial.map (algebraMap (A ⧸ I ^ n)
        (Localization.Away f ⧸ (I ^ n).map (algebraMap A (Localization.Away f)))) p) =
    MvPolynomial.map (coefficientQuotientMap (B := Localization.Away f) I n) p
  rw [MvPolynomial.map_map, quotAwayPowEquiv_comp_algebraMap]

/-- The image of the constant `f` in the restricted power series ring over `A[1/f]` is
invertible. -/
public theorem isUnit_restrictedPowerSeriesMap_coefficientRingHom (I : Ideal A) (σ : Type v)
    (f : A) :
    IsUnit (restrictedPowerSeriesMap (B := Localization.Away f) I σ
      (RestrictedPowerSeries.coefficientRingHom I σ f)) := by
  rw [restrictedPowerSeriesMap_coefficientRingHom]
  exact (IsLocalization.Away.algebraMap_isUnit f).map
    (RestrictedPowerSeries.coefficientRingHom (I.map (algebraMap A (Localization.Away f))) σ)

/-- **Inverting a constant in the coefficients of a restricted power series ring.**  The
canonical map from the localization of `A{σ}` away from `f` to the restricted power series ring
over `A[1/f]`. -/
public noncomputable def awayRestrictedPowerSeriesMap (I : Ideal A) (σ : Type v) (f : A) :
    Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f) →+*
      RestrictedPowerSeries (I.map (algebraMap A (Localization.Away f))) σ :=
  IsLocalization.Away.lift (RestrictedPowerSeries.coefficientRingHom I σ f)
    (isUnit_restrictedPowerSeriesMap_coefficientRingHom I σ f)

/-- The canonical map out of the localization restricts to the coefficient reduction on
`A{σ}`, which pins it down. -/
@[simp]
public theorem awayRestrictedPowerSeriesMap_algebraMap (I : Ideal A) (σ : Type v) (f : A)
    (x : RestrictedPowerSeries I σ) :
    awayRestrictedPowerSeriesMap I σ f
        (algebraMap (RestrictedPowerSeries I σ)
          (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)) x) =
      restrictedPowerSeriesMap I σ x :=
  IsLocalization.Away.lift_eq
    (S := Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f))
    (RestrictedPowerSeries.coefficientRingHom I σ f)
    (isUnit_restrictedPowerSeriesMap_coefficientRingHom I σ f) x

/-- Level `n` of the canonical map `A{σ}[1/f] → (A[1/f]){σ}`. -/
public noncomputable abbrev awayCoefficientProjection (I : Ideal A) (σ : Type v) (f : A) (n : ℕ) :
    Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f) →+*
      MvPolynomial σ (Localization.Away f ⧸ (I.map (algebraMap A (Localization.Away f))) ^ n) :=
  (RestrictedPowerSeries.coefficientProjection
    (I.map (algebraMap A (Localization.Away f))) σ n).comp (awayRestrictedPowerSeriesMap I σ f)

/-- On the image of `A{σ}` the level `n` component is coefficientwise reduction. -/
@[simp]
public theorem awayCoefficientProjection_algebraMap (I : Ideal A) (σ : Type v) (f : A) (n : ℕ)
    (x : RestrictedPowerSeries I σ) :
    awayCoefficientProjection I σ f n
        (algebraMap (RestrictedPowerSeries I σ)
          (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)) x) =
      MvPolynomial.map (coefficientQuotientMap (B := Localization.Away f) I n)
        (RestrictedPowerSeries.coefficientProjection I σ n x) := by
  show RestrictedPowerSeries.coefficientProjection _ σ n
    (awayRestrictedPowerSeriesMap I σ f (algebraMap _ _ x)) = _
  rw [awayRestrictedPowerSeriesMap_algebraMap]
  exact coefficientProjection_restrictedPowerSeriesMap I σ n x

/-- The level `n` reduction of the constant `f` is the constant `f`. -/
private theorem coefficientProjection_coefficientRingHom (I : Ideal A) (σ : Type v) (f : A)
    (n : ℕ) :
    RestrictedPowerSeries.coefficientProjection I σ n
        (RestrictedPowerSeries.coefficientRingHom I σ f) =
      MvPolynomial.C (Ideal.Quotient.mk (I ^ n) f) :=
  RestrictedPowerSeries.coefficientProjection_algebraMap I σ n f

/-- Every power of the constant `f` in `(A ⧸ Iⁿ){σ}` is the level `n` reduction of a power of
the constant `f` in `A{σ}`. -/
private theorem exists_coefficientProjection_pow_eq (I : Ideal A) (σ : Type v) (f : A) (n : ℕ)
    (t : Submonoid.powers
      (MvPolynomial.C (Ideal.Quotient.mk (I ^ n) f) : MvPolynomial σ (A ⧸ I ^ n))) :
    ∃ k : ℕ, RestrictedPowerSeries.coefficientProjection I σ n
      (RestrictedPowerSeries.coefficientRingHom I σ f ^ k) = t := by
  obtain ⟨k, hk⟩ := t.2
  exact ⟨k, by rw [map_pow, coefficientProjection_coefficientRingHom]; exact hk⟩

/-- **The level `n` component of `A{σ}[1/f] → (A[1/f]){σ}` is surjective.**  Every polynomial
over `A[1/f] ⧸ (I · A[1/f])ⁿ` is a quotient of a polynomial over `A ⧸ Iⁿ` by a power of the
constant `f`, and both of those are in the image. -/
public theorem surjective_awayCoefficientProjection (I : Ideal A) (σ : Type v) (f : A) (n : ℕ) :
    Function.Surjective (awayCoefficientProjection I σ f n) := by
  have hloc := isLocalization_mvPolynomial_coefficientQuotientAway I f n σ
  intro u
  obtain ⟨⟨p, t⟩, hpt⟩ := IsLocalization.surj
    (Submonoid.powers
      (MvPolynomial.C (Ideal.Quotient.mk (I ^ n) f) : MvPolynomial σ (A ⧸ I ^ n))) u
  obtain ⟨k, hgk⟩ := exists_coefficientProjection_pow_eq I σ f n t
  obtain ⟨x, hx⟩ := RestrictedPowerSeries.coefficientProjection_surjective I σ n p
  set g := RestrictedPowerSeries.coefficientRingHom I σ f with hg
  refine ⟨IsLocalization.mk' (Localization.Away g) x
    (⟨g ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers g), ?_⟩
  have hspec := IsLocalization.mk'_spec (Localization.Away g) x
    (⟨g ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers g)
  have hmul := congrArg (awayCoefficientProjection I σ f n) hspec
  rw [map_mul, awayCoefficientProjection_algebraMap, awayCoefficientProjection_algebraMap,
    hx] at hmul
  rw [show ((⟨g ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers g) : RestrictedPowerSeries I σ) = g ^ k from rfl,
    hgk] at hmul
  have hunit : IsUnit (algebraMap (MvPolynomial σ (A ⧸ I ^ n))
      (MvPolynomial σ (Localization.Away f ⧸
        (I.map (algebraMap A (Localization.Away f))) ^ n)) (t : _)) :=
    IsLocalization.map_units _ t
  refine (IsUnit.mul_left_inj hunit).mp ?_
  rw [hpt]
  exact hmul

/-- The extension of the coefficient ideal of `A{σ}` to the localization away from `f`: the
ideal of definition of the completed principal localization. -/
public noncomputable def awayCoefficientIdeal (I : Ideal A) (σ : Type v) (f : A) :
    Ideal (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)) :=
  (RestrictedPowerSeries.coefficientIdeal I σ).map
    (algebraMap (RestrictedPowerSeries I σ)
      (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)))

/-- The ideal of definition of the completed principal localization is the extension of the
coefficient ideal. -/
public theorem awayCoefficientIdeal_eq (I : Ideal A) (σ : Type v) (f : A) :
    awayCoefficientIdeal I σ f =
      (RestrictedPowerSeries.coefficientIdeal I σ).map
        (algebraMap (RestrictedPowerSeries I σ)
          (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f))) := rfl

/-- **The kernel of the level `n` component of `A{σ}[1/f] → (A[1/f]){σ}`.**  It is the `n`-th
power of the extended coefficient ideal, provided the coefficient ideal is finitely
generated. -/
public theorem ker_awayCoefficientProjection (I : Ideal A) (hI : I.FG) (σ : Type v) (f : A)
    (n : ℕ) :
    RingHom.ker (awayCoefficientProjection I σ f n) = (awayCoefficientIdeal I σ f) ^ n := by
  rw [awayCoefficientIdeal_eq]
  have hloc := isLocalization_mvPolynomial_coefficientQuotientAway I f n σ
  set g := RestrictedPowerSeries.coefficientRingHom I σ f with hg
  set ψ := algebraMap (RestrictedPowerSeries I σ) (Localization.Away g) with hψ
  have hpow : ((RestrictedPowerSeries.coefficientIdeal I σ).map ψ) ^ n =
      ((RestrictedPowerSeries.coefficientIdeal I σ) ^ n).map ψ :=
    (Ideal.map_pow ψ _ n).symm
  have hmem : ∀ y : RestrictedPowerSeries I σ,
      y ∈ (RestrictedPowerSeries.coefficientIdeal I σ) ^ n →
        ψ y ∈ ((RestrictedPowerSeries.coefficientIdeal I σ).map ψ) ^ n := by
    intro y hy
    rw [hpow]
    exact Ideal.mem_map_of_mem _ hy
  apply le_antisymm
  · intro s hs
    rw [RingHom.mem_ker] at hs
    obtain ⟨⟨x, m⟩, hxm⟩ := IsLocalization.surj (Submonoid.powers g) s
    have hzero : algebraMap (MvPolynomial σ (A ⧸ I ^ n))
        (MvPolynomial σ (Localization.Away f ⧸
          (I.map (algebraMap A (Localization.Away f))) ^ n))
        (RestrictedPowerSeries.coefficientProjection I σ n x) = 0 := by
      have h := congrArg (awayCoefficientProjection I σ f n) hxm
      rw [map_mul, hs, zero_mul, awayCoefficientProjection_algebraMap] at h
      exact h.symm
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers
        (MvPolynomial.C (Ideal.Quotient.mk (I ^ n) f) : MvPolynomial σ (A ⧸ I ^ n)))
      (S := MvPolynomial σ (Localization.Away f ⧸
        (I.map (algebraMap A (Localization.Away f))) ^ n)) _).mp hzero
    obtain ⟨j, hj⟩ := exists_coefficientProjection_pow_eq I σ f n t
    have hjx : RestrictedPowerSeries.coefficientProjection I σ n (g ^ j * x) = 0 := by
      rw [map_mul, hj]
      exact ht
    have hjmem : g ^ j * x ∈ (RestrictedPowerSeries.coefficientIdeal I σ) ^ n := by
      rw [← RestrictedPowerSeries.ker_coefficientProjection I hI σ n, RingHom.mem_ker]
      exact hjx
    have hunitg : IsUnit (ψ g) := by
      rw [hψ, hg]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hx : ψ x ∈ ((RestrictedPowerSeries.coefficientIdeal I σ).map ψ) ^ n := by
      have h := hmem _ hjmem
      rw [map_mul, map_pow, Ideal.unit_mul_mem_iff_mem _ (hunitg.pow j)] at h
      exact h
    rw [← Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units (Localization.Away g) m), hxm]
    exact hx
  · rw [hpow, Ideal.map_le_iff_le_comap]
    intro y hy
    have hy0 : RestrictedPowerSeries.coefficientProjection I σ n y = 0 :=
      RingHom.mem_ker.mp ((RestrictedPowerSeries.ker_coefficientProjection I hI σ n).ge hy)
    rw [Ideal.mem_comap, RingHom.mem_ker, hψ, awayCoefficientProjection_algebraMap, hy0,
      map_zero]

/-- **Localizing away from a constant commutes with the coefficient quotients.**  The level `n`
reduction identifies the localization of `A{σ}` away from `f`, modulo the `n`-th power of the
extended coefficient ideal, with the polynomial ring over `A[1/f] ⧸ (I · A[1/f])ⁿ`. -/
public noncomputable def quotientAwayCoefficientIdealPowEquiv (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) (n : ℕ) :
    Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f) ⧸
        (awayCoefficientIdeal I σ f) ^ n ≃+*
      MvPolynomial σ (Localization.Away f ⧸
        (I.map (algebraMap A (Localization.Away f))) ^ n) :=
  (Ideal.quotEquivOfEq (ker_awayCoefficientProjection I hI σ f n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_awayCoefficientProjection I σ f n))

/-- The identification of the localized coefficient quotient is induced by the level `n`
component of the canonical map. -/
@[simp]
public theorem quotientAwayCoefficientIdealPowEquiv_mk (I : Ideal A) (hI : I.FG) (σ : Type v)
    (f : A) (n : ℕ)
    (s : Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)) :
    quotientAwayCoefficientIdealPowEquiv I hI σ f n (Ideal.Quotient.mk _ s) =
      awayCoefficientProjection I σ f n s := rfl

/-- Level `n` of the canonical map commutes with the transition maps between the coefficient
quotients. -/
private theorem coefficientTransition_awayCoefficientProjection (I : Ideal A) (σ : Type v)
    (f : A) {m n : ℕ} (hmn : m ≤ n)
    (s : Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)) :
    RestrictedPowerSeries.coefficientTransition
        (I.map (algebraMap A (Localization.Away f))) σ hmn
        (awayCoefficientProjection I σ f n s) =
      awayCoefficientProjection I σ f m s :=
  (awayRestrictedPowerSeriesMap I σ f s).property hmn

/-- The identifications of the localized coefficient quotients commute with the transition
maps. -/
private theorem coefficientTransition_quotientAwayCoefficientIdealPowEquiv (I : Ideal A)
    (hI : I.FG) (σ : Type v) (f : A) {m n : ℕ} (hmn : m ≤ n)
    (z : Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f) ⧸
      (awayCoefficientIdeal I σ f) ^ n) :
    RestrictedPowerSeries.coefficientTransition
        (I.map (algebraMap A (Localization.Away f))) σ hmn
        (quotientAwayCoefficientIdealPowEquiv I hI σ f n z) =
      quotientAwayCoefficientIdealPowEquiv I hI σ f m
        (Ideal.Quotient.factorPow (awayCoefficientIdeal I σ f) hmn z) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact coefficientTransition_awayCoefficientProjection I σ f hmn s

/-- The family of level `n` coefficient reductions attached to an element of the completion of
`A{σ}[1/f]` is compatible with the transition maps. -/
public theorem awayCompletionFamily_compatible (I : Ideal A) (hI : I.FG) (σ : Type v) (f : A)
    (x : AdicCompletion (awayCoefficientIdeal I σ f)
      (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)))
    {m n : ℕ} (hmn : m ≤ n) :
    RestrictedPowerSeries.coefficientTransition
        (I.map (algebraMap A (Localization.Away f))) σ hmn
        (quotientAwayCoefficientIdealPowEquiv I hI σ f n
          (AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n x)) =
      quotientAwayCoefficientIdealPowEquiv I hI σ f m
        (AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) m x) := by
  have h := coefficientTransition_quotientAwayCoefficientIdealPowEquiv I hI σ f hmn
    (AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n x)
  rwa [AdicCompletion.factorPow_evalₐ] at h

/-- **The completion of `A{σ}[1/f]` along the extended coefficient ideal is the restricted power
series ring over `A[1/f]`.**  The canonical map reads off, at every level, the identification of
the level `n` coefficient quotients. -/
public noncomputable def completedAwayRestrictedPowerSeriesMap (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) :
    AdicCompletion (awayCoefficientIdeal I σ f)
        (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)) →+*
      RestrictedPowerSeries (I.map (algebraMap A (Localization.Away f))) σ where
  toFun x :=
    ⟨fun n => quotientAwayCoefficientIdealPowEquiv I hI σ f n
      (AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n x),
      by intro m n hmn; exact awayCompletionFamily_compatible I hI σ f x hmn⟩
  map_one' := Subtype.ext (funext fun n =>
    ((quotientAwayCoefficientIdealPowEquiv I hI σ f n).toRingHom.comp
      (AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n).toRingHom).map_one)
  map_mul' x y := Subtype.ext (funext fun n =>
    ((quotientAwayCoefficientIdealPowEquiv I hI σ f n).toRingHom.comp
      (AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n).toRingHom).map_mul x y)
  map_zero' := Subtype.ext (funext fun n =>
    ((quotientAwayCoefficientIdealPowEquiv I hI σ f n).toRingHom.comp
      (AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n).toRingHom).map_zero)
  map_add' x y := Subtype.ext (funext fun n =>
    ((quotientAwayCoefficientIdealPowEquiv I hI σ f n).toRingHom.comp
      (AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n).toRingHom).map_add x y)

/-- Level `n` of the canonical map out of the completion is the identification of the level `n`
coefficient quotients, which pins it down. -/
@[simp]
public theorem coefficientProjection_completedAwayRestrictedPowerSeriesMap (I : Ideal A)
    (hI : I.FG) (σ : Type v) (f : A) (n : ℕ)
    (x : AdicCompletion (awayCoefficientIdeal I σ f)
      (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f))) :
    RestrictedPowerSeries.coefficientProjection (I.map (algebraMap A (Localization.Away f))) σ n
        (completedAwayRestrictedPowerSeriesMap I hI σ f x) =
      quotientAwayCoefficientIdealPowEquiv I hI σ f n
        (AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n x) := rfl

/-- The inverses of the level `n` identifications form a compatible family. -/
public theorem factorPow_symm_quotientAwayCoefficientIdealPowEquiv (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) {m n : ℕ} (hmn : m ≤ n)
    (y : RestrictedPowerSeries (I.map (algebraMap A (Localization.Away f))) σ) :
    Ideal.Quotient.factorPow (awayCoefficientIdeal I σ f) hmn
        ((quotientAwayCoefficientIdealPowEquiv I hI σ f n).symm
          (RestrictedPowerSeries.coefficientProjection
            (I.map (algebraMap A (Localization.Away f))) σ n y)) =
      (quotientAwayCoefficientIdealPowEquiv I hI σ f m).symm
        (RestrictedPowerSeries.coefficientProjection
          (I.map (algebraMap A (Localization.Away f))) σ m y) := by
  refine (quotientAwayCoefficientIdealPowEquiv I hI σ f m).injective ?_
  refine (coefficientTransition_quotientAwayCoefficientIdealPowEquiv I hI σ f hmn _).symm.trans
    ?_
  refine (congrArg (RestrictedPowerSeries.coefficientTransition
    (I.map (algebraMap A (Localization.Away f))) σ hmn)
      ((quotientAwayCoefficientIdealPowEquiv I hI σ f n).apply_symm_apply _)).trans ?_
  exact (y.property hmn).trans
    ((quotientAwayCoefficientIdealPowEquiv I hI σ f m).apply_symm_apply _).symm

/-- **The restricted power series ring over `A[1/f]` maps back to the completion of
`A{σ}[1/f]`.**  The inverses of the level `n` identifications form a compatible family of ring
maps into the coefficient quotients, hence a map into the completion. -/
public noncomputable def completedAwayRestrictedPowerSeriesInv (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) :
    RestrictedPowerSeries (I.map (algebraMap A (Localization.Away f))) σ →+*
      AdicCompletion (awayCoefficientIdeal I σ f)
        (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)) :=
  AdicCompletion.liftRingHom (awayCoefficientIdeal I σ f)
    (fun n => (quotientAwayCoefficientIdealPowEquiv I hI σ f n).symm.toRingHom.comp
      (RestrictedPowerSeries.coefficientProjection
        (I.map (algebraMap A (Localization.Away f))) σ n))
    (fun hmn => RingHom.ext fun y =>
      factorPow_symm_quotientAwayCoefficientIdealPowEquiv I hI σ f hmn y)

/-- Level `n` of the backward map is the inverse of the level `n` identification. -/
@[simp]
public theorem evalₐ_completedAwayRestrictedPowerSeriesInv (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) (n : ℕ)
    (y : RestrictedPowerSeries (I.map (algebraMap A (Localization.Away f))) σ) :
    AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n
        (completedAwayRestrictedPowerSeriesInv I hI σ f y) =
      (quotientAwayCoefficientIdealPowEquiv I hI σ f n).symm
        (RestrictedPowerSeries.coefficientProjection
          (I.map (algebraMap A (Localization.Away f))) σ n y) :=
  AdicCompletion.evalₐ_liftRingHom (awayCoefficientIdeal I σ f)
    (fun n => (quotientAwayCoefficientIdealPowEquiv I hI σ f n).symm.toRingHom.comp
      (RestrictedPowerSeries.coefficientProjection
        (I.map (algebraMap A (Localization.Away f))) σ n))
    (fun hmn => RingHom.ext fun y =>
      factorPow_symm_quotientAwayCoefficientIdealPowEquiv I hI σ f hmn y) n y

/-- **The completed principal localization of `A{σ}` is `(A[1/f]){σ}`.**  The canonical map from
the completion of `A{σ}[1/f]` along the extended coefficient ideal to the restricted power series
ring over `A[1/f]` is an isomorphism, with inverse the map assembled from the inverses of the
level `n` identifications. -/
public theorem bijective_completedAwayRestrictedPowerSeriesMap (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) :
    Function.Bijective (completedAwayRestrictedPowerSeriesMap I hI σ f) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨completedAwayRestrictedPowerSeriesInv I hI σ f, fun x => ?_, fun y => ?_⟩
  · refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_completedAwayRestrictedPowerSeriesInv,
      coefficientProjection_completedAwayRestrictedPowerSeriesMap,
      RingEquiv.symm_apply_apply]
  · refine RestrictedPowerSeries.idealSystem_ext fun n => ?_
    exact (congrArg (quotientAwayCoefficientIdealPowEquiv I hI σ f n)
      (evalₐ_completedAwayRestrictedPowerSeriesInv I hI σ f n y)).trans
        ((quotientAwayCoefficientIdealPowEquiv I hI σ f n).apply_symm_apply _)

/-- **Stacks 0GGG, principal localization of a restricted power series ring.**  The completed
principal localization of `A{σ}` at `f` is the restricted power series ring over the completed
principal localization of `A` at `f`: the composite of the canonical map out of the completion
with the canonical map of restricted power series rings is an isomorphism. -/
public theorem bijective_restrictedPowerSeriesMap_comp_completedAway (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) :
    Function.Bijective
      ((restrictedPowerSeriesMap
          (B := AdicCompletion (I.map (algebraMap A (Localization.Away f)))
            (Localization.Away f))
          (I.map (algebraMap A (Localization.Away f))) σ).comp
        (completedAwayRestrictedPowerSeriesMap I hI σ f)) :=
  (bijective_restrictedPowerSeriesMap_completedAway I hI f σ).comp
    (bijective_completedAwayRestrictedPowerSeriesMap I hI σ f)

/-- **On the image of `A{σ}` the map out of the completion is coefficientwise reduction.**  A
restricted power series over `A`, viewed in the completion of `A{σ}[1/f]`, is sent to its
coefficientwise image in `(A[1/f]){σ}`. -/
@[simp]
public theorem completedAwayRestrictedPowerSeriesMap_algebraMap (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) (x : RestrictedPowerSeries I σ) :
    completedAwayRestrictedPowerSeriesMap I hI σ f
        (algebraMap (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f))
          (AdicCompletion (awayCoefficientIdeal I σ f)
            (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)))
          (algebraMap (RestrictedPowerSeries I σ)
            (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)) x)) =
      restrictedPowerSeriesMap (B := Localization.Away f) I σ x := by
  refine RestrictedPowerSeries.idealSystem_ext fun n => ?_
  rw [coefficientProjection_completedAwayRestrictedPowerSeriesMap,
    show AdicCompletion.evalₐ (awayCoefficientIdeal I σ f) n
        (algebraMap _ _ (algebraMap (RestrictedPowerSeries I σ) _ x)) =
      Ideal.Quotient.mk ((awayCoefficientIdeal I σ f) ^ n)
        (algebraMap (RestrictedPowerSeries I σ) _ x) from rfl,
    quotientAwayCoefficientIdealPowEquiv_mk, awayCoefficientProjection_algebraMap,
    coefficientProjection_restrictedPowerSeriesMap]

/-- **The identification of `A\{σ\}_{\{f\}}` with `A_{\{f\}}\{σ\}` is compatible with the maps
from `A{σ}`.**  Composing the isomorphism of
`TopologicalRing.bijective_restrictedPowerSeriesMap_comp_completedAway` with the structure map
of the completed principal localization gives the two-step coefficientwise reduction
`A{σ} → (A[1/f]){σ} → A_{\{f\}}{σ}`.

This is what makes the isomorphism usable in a square: a flatness or primality statement about
the structure map `A{σ} → A{σ}_{\{f\}}` transports to one about the coefficientwise map into
`A_{\{f\}}{σ}`, without needing to know how the isomorphism behaves off the image of `A{σ}`. -/
public theorem restrictedPowerSeriesMap_comp_completedAway_comp_algebraMap (I : Ideal A)
    (hI : I.FG) (σ : Type v) (f : A) :
    ((restrictedPowerSeriesMap
          (B := AdicCompletion (I.map (algebraMap A (Localization.Away f)))
            (Localization.Away f))
          (I.map (algebraMap A (Localization.Away f))) σ).comp
        (completedAwayRestrictedPowerSeriesMap I hI σ f)).comp
        (algebraMap (RestrictedPowerSeries I σ)
          (AdicCompletion (awayCoefficientIdeal I σ f)
            (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)))) =
      (restrictedPowerSeriesMap
          (B := AdicCompletion (I.map (algebraMap A (Localization.Away f)))
            (Localization.Away f))
          (I.map (algebraMap A (Localization.Away f))) σ).comp
        (restrictedPowerSeriesMap (B := Localization.Away f) I σ) := by
  refine RingHom.ext fun x => ?_
  show restrictedPowerSeriesMap _ σ (completedAwayRestrictedPowerSeriesMap I hI σ f
      (algebraMap (RestrictedPowerSeries I σ) _ x)) =
    restrictedPowerSeriesMap _ σ (restrictedPowerSeriesMap (B := Localization.Away f) I σ x)
  rw [IsScalarTower.algebraMap_apply (RestrictedPowerSeries I σ)
      (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f))
      (AdicCompletion (awayCoefficientIdeal I σ f)
        (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f))),
    completedAwayRestrictedPowerSeriesMap_algebraMap]

end

end TopologicalRing

end
