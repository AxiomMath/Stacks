module

public import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.MinimalPrimeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.PrimeDivisorChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fraction field of a stalk modulo a minimal prime is a residue field

The chart form of the key formula of Stacks 0EQV reads orders of vanishing along a prime divisor
through the minimal primes `𝔭` of the local ring `O = 𝒪_{W', y}` of a chart, in the fraction
field `Frac(O/𝔭)` (`Ring.minimalPrimeOrd`), while the restriction to the divisor reads the
same functions in the residue field `κ(q')` at the generic point `q'` of the branch through
`𝔭`.  This file identifies the two fields and the two readings.

## Main definitions

* `Ring.quotientToLocalizationAtPrime`: for a prime `𝔭` of `O` and a localization `L` of `O` at
  `𝔭` which is a field, the induced injection `O/𝔭 → L`.
* `Ring.fractionRingQuotientEquiv`: **the identification `Frac(O/𝔭) ≃ L`**.
* `Ring.minimalPrimeLocalizationMap`: for a minimal prime `𝔭` and the total ring of fractions
  `K` of `O`, the map `K → L` induced by `O → L`.
* `AlgebraicGeometry.Scheme.primeOfSpecializes`: the prime of `𝒪_{T, y}` of a generization
  `z ⤳ y` of points of a scheme.
* `AlgebraicGeometry.Scheme.fractionRingQuotientEquivResidueField`: for such a generization with
  `𝒪_{T, z}` a field, the identification `Frac(𝒪_{T, y}/𝔭) ≃ κ(z)` at the prime `𝔭` of `z`.
* `AlgebraicGeometry.Scheme.totalFractionToResidueFieldOfSpecializes`: the reading
  `Q(𝒪_{T, y}) → κ(z)` of the total ring of fractions.
* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartResidueFieldEquiv`: the isomorphism
  `κ(q) ≃ κ(q')` of residue fields along the closed immersion `W ×_X Z → W`, at a point `q'` of
  `W ×_X Z` over `q`.

## Main results

* `Ring.ker_algebraMap_eq_of_isLocalization_atPrime`: the kernel of `O → L` is `𝔭`.
* `Ring.isFractionRing_quotient_of_isLocalization_atPrime`: `L` is a fraction field of `O/𝔭`.
* `Ring.fractionRingQuotientEquiv_comp_minimalPrimeFractionMap`: **the reading
  `K → Frac(O/𝔭)` of `Ring.minimalPrimeOrd`, followed by `Frac(O/𝔭) ≃ L`, is the reading
  `K → L`.**
* `Ring.mem_minimalPrimes_of_isLocalization_atPrime`: a prime at which the localization is a
  field is minimal.
* `AlgebraicGeometry.Scheme.isLocalization_atPrime_residueField_of_specializes` and
  `AlgebraicGeometry.Scheme.primeOfSpecializes_mem_minimalPrimes`: for `z ⤳ y` with `𝒪_{T, z}`
  a field, `κ(z)` is the localization of `𝒪_{T, y}` at the prime of `z`, and that prime is
  minimal.
* `AlgebraicGeometry.Scheme.fractionRingQuotientEquivResidueField_minimalPrimeFractionMap`: the
  scheme form of the compatibility of the two readings.
* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartResidueFieldEquiv_residue`: the
  isomorphism `κ(q) ≃ κ(q')` is induced by the stalk map.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 02MA](https://stacks.math.columbia.edu/tag/02MA)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open scoped nonZeroDivisors

universe u

namespace Ring

/-! ### A localization at a prime which is a field -/

section AtPrime

variable {O : Type*} [CommRing O] (p : Ideal O) [p.IsPrime] (L : Type*) [Field L] [Algebra O L]
    [IsLocalization.AtPrime L p]

/-- **The kernel of a localization at a prime which is a field is that prime.**  An element maps
into the maximal ideal of the localization exactly when it lies in the prime, and the maximal
ideal of a field is zero. -/
theorem ker_algebraMap_eq_of_isLocalization_atPrime : RingHom.ker (algebraMap O L) = p := by
  ext x
  rw [RingHom.mem_ker, ← IsLocalization.AtPrime.to_map_mem_maximal_iff L p x,
    IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]

/-- The injection `O/𝔭 → L` induced by a localization `L` of `O` at `𝔭` which is a field. -/
def quotientToLocalizationAtPrime : O ⧸ p →+* L :=
  Ideal.Quotient.lift p (algebraMap O L) fun _ hx ↦
    (RingHom.mem_ker).1 ((ker_algebraMap_eq_of_isLocalization_atPrime p L).ge hx)

/-- The injection `O/𝔭 → L` on the class of an element. -/
theorem quotientToLocalizationAtPrime_mk (x : O) :
    quotientToLocalizationAtPrime p L (Ideal.Quotient.mk p x) = algebraMap O L x :=
  Ideal.Quotient.lift_mk _ _ _

/-- The map `O/𝔭 → L` is injective. -/
theorem injective_quotientToLocalizationAtPrime :
    Function.Injective (quotientToLocalizationAtPrime p L) :=
  RingHom.lift_injective_of_ker_le_ideal p _
    (ker_algebraMap_eq_of_isLocalization_atPrime p L).le

/-- **A localization at a prime which is a field is a fraction field of the quotient by that
prime**, for the algebra structure given by `Ring.quotientToLocalizationAtPrime`. -/
@[ega "0 1.2.3" "special case", ega "0 7.6.17" "special case", ega "I 1.1.1" "special case"]
theorem isFractionRing_quotient_of_isLocalization_atPrime :
    letI := (quotientToLocalizationAtPrime p L).toAlgebra
    IsFractionRing (O ⧸ p) L := by
  let := (quotientToLocalizationAtPrime p L).toAlgebra
  have : FaithfulSMul (O ⧸ p) L :=
    (faithfulSMul_iff_algebraMap_injective (O ⧸ p) L).2
      (injective_quotientToLocalizationAtPrime p L)
  refine IsFractionRing.of_field (O ⧸ p) L fun z ↦ ?_
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (M := p.primeCompl) z
  refine ⟨Ideal.Quotient.mk p x, Ideal.Quotient.mk p (s : O), ?_⟩
  change _ = quotientToLocalizationAtPrime p L _ / quotientToLocalizationAtPrime p L _
  rw [quotientToLocalizationAtPrime_mk, quotientToLocalizationAtPrime_mk]
  exact (eq_div_iff (IsLocalization.map_units L s).ne_zero).2 (IsLocalization.mk'_spec L x s)

/-- **The identification `Frac(O/𝔭) ≃ L`** for a localization `L` of `O` at a prime `𝔭` which is
a field: both are fraction fields of `O/𝔭`. -/
@[ega "0 1.2.3" "special case", ega "0 7.6.17" "special case"]
def fractionRingQuotientEquiv : FractionRing (O ⧸ p) ≃+* L :=
  letI := (quotientToLocalizationAtPrime p L).toAlgebra
  haveI := isFractionRing_quotient_of_isLocalization_atPrime p L
  (IsLocalization.algEquiv (O ⧸ p)⁰ (FractionRing (O ⧸ p)) L).toRingEquiv

/-- The identification `Frac(O/𝔭) ≃ L` on the class of an element of `O`. -/
theorem fractionRingQuotientEquiv_algebraMap (x : O) :
    fractionRingQuotientEquiv p L
        (algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p x)) =
      algebraMap O L x := by
  let := (quotientToLocalizationAtPrime p L).toAlgebra
  have := isFractionRing_quotient_of_isLocalization_atPrime p L
  refine (IsLocalization.algEquiv_apply (O ⧸ p)⁰ (FractionRing (O ⧸ p)) L _).trans ?_
  refine (IsLocalization.map_eq _ _).trans ?_
  exact quotientToLocalizationAtPrime_mk p L x

include L in
/-- **A prime at which the localization is a field is minimal**: the localization has dimension
the height of the prime, and a field has dimension zero. -/
theorem mem_minimalPrimes_of_isLocalization_atPrime : p ∈ minimalPrimes O := by
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height p L
  rw [ringKrullDim_eq_zero_of_isField (Field.toIsField L)] at h
  exact Ideal.height_eq_zero_iff.1 (by exact_mod_cast h.symm)

end AtPrime

/-! ### The two readings of a fraction at a minimal prime -/

section MinimalPrime

variable {O : Type*} [CommRing O] (p : Ideal O) [p.IsPrime] (hp : p ∈ minimalPrimes O)
    (L : Type*) [Field L] [Algebra O L] [IsLocalization.AtPrime L p]
    (K : Type*) [CommRing K] [Algebra O K] [IsFractionRing O K]

include hp in
/-- A nonzerodivisor of `O` becomes a unit in the localization at a minimal prime: minimal
primes consist of zerodivisors. -/
theorem isUnit_algebraMap_of_mem_nonZeroDivisors {s : O} (hs : s ∈ O⁰) :
    IsUnit (algebraMap O L s) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff L p s).2
    fun hsp ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hsp hp hs

/-- **The reading of a fraction in the localization at a minimal prime**: the map `K → L` from
the total ring of fractions of `O` induced by `O → L`. -/
def minimalPrimeLocalizationMap : K →+* L :=
  IsLocalization.lift (M := O⁰) (S := K) (g := algebraMap O L)
    fun s ↦ isUnit_algebraMap_of_mem_nonZeroDivisors p hp L s.2

/-- The reading `K → L` is `O → L` on `O`. -/
theorem minimalPrimeLocalizationMap_algebraMap (x : O) :
    minimalPrimeLocalizationMap p hp L K (algebraMap O K x) = algebraMap O L x :=
  IsLocalization.lift_eq _ x

/-- **The reading `K → Frac(O/𝔭)` of `Ring.minimalPrimeOrd`, followed by `Frac(O/𝔭) ≃ L`, is the
reading `K → L`**: both are ring maps out of the total ring of fractions agreeing on `O`. -/
theorem fractionRingQuotientEquiv_comp_minimalPrimeFractionMap :
    (fractionRingQuotientEquiv p L).toRingHom.comp
        (minimalPrimeFractionMap (K := K) ⟨p, hp⟩) =
      minimalPrimeLocalizationMap p hp L K := by
  refine IsLocalization.ringHom_ext O⁰ (RingHom.ext fun x ↦ ?_)
  change fractionRingQuotientEquiv p L
      (minimalPrimeFractionMap (K := K) ⟨p, hp⟩ (algebraMap O K x)) =
    minimalPrimeLocalizationMap p hp L K (algebraMap O K x)
  rw [minimalPrimeLocalizationMap_algebraMap]
  refine Eq.trans (congrArg (fractionRingQuotientEquiv p L) (IsLocalization.map_eq _ x)) ?_
  exact fractionRingQuotientEquiv_algebraMap p L x

/-- The compatibility of the two readings, on elements. -/
theorem fractionRingQuotientEquiv_minimalPrimeFractionMap (f : K) :
    fractionRingQuotientEquiv p L (minimalPrimeFractionMap (K := K) ⟨p, hp⟩ f) =
      minimalPrimeLocalizationMap p hp L K f :=
  RingHom.congr_fun (fractionRingQuotientEquiv_comp_minimalPrimeFractionMap p hp L K) f

end MinimalPrime

end Ring

/-! ### At a generization of a point of a scheme -/

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {y z : T} (h : z ⤳ y)

/-- The map `𝒪_{T, y} → κ(z)` at a generization `z ⤳ y`: the generization map of stalks followed
by the residue map at `z`. -/
def stalkToResidueFieldOfSpecializes : T.presheaf.stalk y →+* T.residueField z :=
  (T.residue z).hom.comp (T.presheaf.stalkSpecializes h).hom

/-- The prime of `𝒪_{T, y}` of a generization `z ⤳ y`: the pullback of the maximal ideal of
`𝒪_{T, z}`. -/
def primeOfSpecializes : Ideal (T.presheaf.stalk y) :=
  (IsLocalRing.maximalIdeal (T.presheaf.stalk z)).comap (T.presheaf.stalkSpecializes h).hom

/-- The ideal `primeOfSpecializes h` of `𝒪_{T, y}` is prime. -/
instance isPrime_primeOfSpecializes : (primeOfSpecializes h).IsPrime :=
  Ideal.comap_isPrime _ _

variable (hz : IsField (T.presheaf.stalk z))

include hz in
/-- The residue map of a local ring which is a field is bijective. -/
theorem bijective_residue_of_isField : Function.Bijective (T.residue z).hom := by
  refine ⟨fun a b hab ↦ ?_, IsLocalRing.residue_surjective⟩
  have hmax := (IsLocalRing.isField_iff_maximalIdeal_eq).1 hz
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hmax, ← IsLocalRing.residue_eq_zero_iff]
  exact (map_sub (T.residue z).hom a b).trans (sub_eq_zero.2 hab)

include hz in
/-- **At a generization `z ⤳ y` with `𝒪_{T, z}` a field, `κ(z)` is the localization of
`𝒪_{T, y}` at the prime of `z`.**  `𝒪_{T, z}` is that localization
(`Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes`) and its residue map is an
isomorphism. -/
theorem isLocalization_atPrime_residueField_of_specializes :
    letI := (stalkToResidueFieldOfSpecializes h).toAlgebra
    IsLocalization.AtPrime (T.residueField z) (primeOfSpecializes h) := by
  let A : Algebra (T.presheaf.stalk y) (T.presheaf.stalk z) :=
    (T.presheaf.stalkSpecializes h).hom.toAlgebra
  let := (stalkToResidueFieldOfSpecializes h).toAlgebra
  have : IsLocalization.AtPrime (T.presheaf.stalk z) (primeOfSpecializes h) :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes h
  let e : T.presheaf.stalk z ≃ₐ[T.presheaf.stalk y] T.residueField z :=
    AlgEquiv.ofBijective
      { (T.residue z).hom with commutes' := fun _ ↦ rfl }
      (bijective_residue_of_isField hz)
  exact IsLocalization.isLocalization_of_algEquiv (primeOfSpecializes h).primeCompl e

include hz in
/-- **The prime of a generization whose local ring is a field is minimal.** -/
theorem primeOfSpecializes_mem_minimalPrimes : primeOfSpecializes h ∈ minimalPrimes _ :=
  let := (stalkToResidueFieldOfSpecializes h).toAlgebra
  have := isLocalization_atPrime_residueField_of_specializes h hz
  Ring.mem_minimalPrimes_of_isLocalization_atPrime (primeOfSpecializes h) (T.residueField z)

/-- **The identification `Frac(𝒪_{T, y}/𝔭) ≃ κ(z)`** at a generization `z ⤳ y` with `𝒪_{T, z}`
a field, `𝔭` being the prime of `z`. -/
def fractionRingQuotientEquivResidueField :
    FractionRing (T.presheaf.stalk y ⧸ primeOfSpecializes h) ≃+* T.residueField z :=
  letI := (stalkToResidueFieldOfSpecializes h).toAlgebra
  haveI := isLocalization_atPrime_residueField_of_specializes h hz
  Ring.fractionRingQuotientEquiv (primeOfSpecializes h) (T.residueField z)

/-- The identification `Frac(𝒪_{T, y}/𝔭) ≃ κ(z)` on the class of an element of `𝒪_{T, y}` is
its image in `κ(z)`. -/
theorem fractionRingQuotientEquivResidueField_algebraMap (a : T.presheaf.stalk y) :
    fractionRingQuotientEquivResidueField h hz
        (algebraMap _ (FractionRing (T.presheaf.stalk y ⧸ primeOfSpecializes h))
          (Ideal.Quotient.mk (primeOfSpecializes h) a)) =
      stalkToResidueFieldOfSpecializes h a :=
  let := (stalkToResidueFieldOfSpecializes h).toAlgebra
  have := isLocalization_atPrime_residueField_of_specializes h hz
  Ring.fractionRingQuotientEquiv_algebraMap (primeOfSpecializes h) (T.residueField z) a

/-- **The reading of the total ring of fractions of `𝒪_{T, y}` at a generization**: the map
`Q(𝒪_{T, y}) → κ(z)` induced by `𝒪_{T, y} → κ(z)`. -/
def totalFractionToResidueFieldOfSpecializes (K : Type*) [CommRing K]
    [Algebra (T.presheaf.stalk y) K] [IsFractionRing (T.presheaf.stalk y) K] :
    K →+* T.residueField z :=
  letI := (stalkToResidueFieldOfSpecializes h).toAlgebra
  haveI := isLocalization_atPrime_residueField_of_specializes h hz
  Ring.minimalPrimeLocalizationMap (primeOfSpecializes h)
    (primeOfSpecializes_mem_minimalPrimes h hz) (T.residueField z) K

/-- The reading `Q(𝒪_{T, y}) → κ(z)` on `𝒪_{T, y}`. -/
theorem totalFractionToResidueFieldOfSpecializes_algebraMap (K : Type*) [CommRing K]
    [Algebra (T.presheaf.stalk y) K] [IsFractionRing (T.presheaf.stalk y) K]
    (a : T.presheaf.stalk y) :
    totalFractionToResidueFieldOfSpecializes h hz K (algebraMap _ K a) =
      stalkToResidueFieldOfSpecializes h a :=
  let := (stalkToResidueFieldOfSpecializes h).toAlgebra
  have := isLocalization_atPrime_residueField_of_specializes h hz
  Ring.minimalPrimeLocalizationMap_algebraMap (primeOfSpecializes h)
    (primeOfSpecializes_mem_minimalPrimes h hz) (T.residueField z) K a

/-- **The two readings at a generization agree.**  For `z ⤳ y` with `𝒪_{T, z}` a field, the
reading `Q(𝒪_{T, y}) → Frac(𝒪_{T, y}/𝔭)` of `Ring.minimalPrimeOrd` at the (minimal) prime `𝔭`
of `z`, followed by `Frac(𝒪_{T, y}/𝔭) ≃ κ(z)`, is the reading `Q(𝒪_{T, y}) → κ(z)`. -/
theorem fractionRingQuotientEquivResidueField_minimalPrimeFractionMap (K : Type*) [CommRing K]
    [Algebra (T.presheaf.stalk y) K] [IsFractionRing (T.presheaf.stalk y) K] (f : K) :
    fractionRingQuotientEquivResidueField h hz
        (Ring.minimalPrimeFractionMap (K := K)
          ⟨primeOfSpecializes h, primeOfSpecializes_mem_minimalPrimes h hz⟩ f) =
      totalFractionToResidueFieldOfSpecializes h hz K f :=
  let := (stalkToResidueFieldOfSpecializes h).toAlgebra
  have := isLocalization_atPrime_residueField_of_specializes h hz
  Ring.fractionRingQuotientEquiv_minimalPrimeFractionMap (primeOfSpecializes h)
    (primeOfSpecializes_mem_minimalPrimes h hz) (T.residueField z) K f

end AlgebraicGeometry.Scheme

/-! ### The residue fields of `W ×_X Z` and of `W` -/

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : PrimeDivisor B S hS X) (W : SmallEtale B S hS X)
    (q' : chartScheme (Z.baseChangeChart B S hS hX W))

/-- **The residue fields of `W ×_X Z` are those of `W`**: at a point `q'` of the base change
chart over `q ∈ W`, the residue field map `κ(q) → κ(q')` of the closed immersion `W ×_X Z → W`
is an isomorphism. -/
def PrimeDivisor.baseChangeChartResidueFieldEquiv :
    (chartScheme W).residueField (Z.baseChangeChartProj B S hS hX W q') ≃+*
      (chartScheme (Z.baseChangeChart B S hS hX W)).residueField q' :=
  haveI := Z.isClosedImmersion_baseChangeChartProj B S hS hX W
  haveI := residueFieldMap_isIso_of_isClosedImmersion (Z.baseChangeChartProj B S hS hX W) q'
  (asIso ((Z.baseChangeChartProj B S hS hX W).residueFieldMap q')).commRingCatIsoToRingEquiv

/-- The isomorphism `κ(q) ≃ κ(q')` sends the residue of a germ to the residue of its image under
the stalk map. -/
theorem PrimeDivisor.baseChangeChartResidueFieldEquiv_residue
    (a : (chartScheme W).presheaf.stalk (Z.baseChangeChartProj B S hS hX W q')) :
    Z.baseChangeChartResidueFieldEquiv B S hS hX W q'
        ((chartScheme W).residue (Z.baseChangeChartProj B S hS hX W q') a) =
      (chartScheme (Z.baseChangeChart B S hS hX W)).residue q'
        ((Z.baseChangeChartProj B S hS hX W).stalkMap q' a) :=
  ConcreteCategory.congr_hom
    (Scheme.residue_residueFieldMap (Z.baseChangeChartProj B S hS hX W) q') a

end AlgebraicGeometry.Space

end
