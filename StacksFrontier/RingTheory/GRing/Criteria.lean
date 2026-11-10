module

public import Mathlib
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.FormallySmooth.RegularLocal
public import StacksFrontier.RingTheory.CompleteLocalRing.PowerSeriesMaps
public import StacksFrontier.RingTheory.Derivation.Extension
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.RingTheory.Flat.FiniteFreeResidueExtension
public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.PowerSeries.IntegrallyClosed
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Criteria for a Noetherian ring to be a G-ring

Criteria for a Noetherian ring to be a G-ring, the ascent of geometric regularity of formal fibres
along quasi-finite ring maps, and the theorem that a complete Noetherian local ring is a G-ring.

## Main definitions

* `geometricallyRegularProperty`: geometric regularity as a property of ring maps.

## Main results

* `isGRing_iff_quotientCompletion_isGeometricallyRegular`: a Noetherian ring is a G-ring if and
  only if, for primes `q ≤ p`, the completion of `(R / q)ₚ` tensored with the residue field at
  `q` is geometrically regular.
* `quasiFinite_preserves_geometricallyRegular_formalFibers_and_isGRing`: geometric regularity
  of formal fibres ascends along a finite-type ring map at a prime where it is quasi-finite, and
  G-rings are preserved by quasi-finite ring maps.
* `isGRing_iff_finiteFree_formalFibers_isRegularRing`: a Noetherian ring is a G-ring if and only
  if every formal fibre of every finite free algebra over it is a regular ring.
* `isGeometricallyRegular_formalFiber_mvPolynomial_mvPowerSeries`: for a polynomial ring `A` in
  finitely many variables over a power-series ring in finitely many variables over a field of
  prime characteristic, the generic formal fibre of `A` at every prime is geometrically regular
  over the fraction field of `A`.
* `isGRing_of_isPrecomplete_maximalIdeal`: a Noetherian local ring complete for its
  maximal-ideal-adic topology is a G-ring.

## References

* [Stacks Project, Tag 07PN](https://stacks.math.columbia.edu/tag/07PN)
* [Stacks Project, Tag 07PP](https://stacks.math.columbia.edu/tag/07PP)
* [Stacks Project, Tag 07PQ](https://stacks.math.columbia.edu/tag/07PQ)
* [Stacks Project, Tag 07PR](https://stacks.math.columbia.edu/tag/07PR)
* [Stacks Project, Tag 07PS](https://stacks.math.columbia.edu/tag/07PS)
-/

open Stacks.DerivationExtension

/-! ### A quotient-completion criterion -/

section

section

open scoped TensorProduct

universe u v w

/-- Geometric regularity as a property of ring maps whose source and target lie in the same
universe. -/
public abbrev geometricallyRegularProperty : RingMapProperty.{u, u} :=
  RingMapProperty.geometricallyRegular

private lemma geometricallyRegularProperty_iff
    {k A : Type u} [Field k] [CommRing A] (f : k →+* A) :
    geometricallyRegularProperty f ↔
      @Algebra.IsGeometricallyRegular k A _ _ f.toAlgebra :=
  RingMapProperty.geometricallyRegular_iff f

private lemma isGRing_iff_isPRing_geometricallyRegular
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔ IsPRing geometricallyRegularProperty R := by
  rw [isPRing_iff]
  simp only [IsGRing]
  constructor
  · rintro ⟨_, h⟩
    refine ⟨inferInstance, fun p => ?_⟩
    rw [formalFibersHave_iff]
    intro q
    let _ : Algebra q.asIdeal.ResidueField
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime p.asIdeal) ⊗[Localization.AtPrime p.asIdeal]
            q.asIdeal.ResidueField) := Algebra.TensorProduct.rightAlgebra
    exact (geometricallyRegularProperty_iff _).mpr <|
      @Algebra.IsGeometricallyRegular.of_algEquiv _ _ _ _ _ _ _ _ ((h p.asIdeal).2 q.asIdeal |>.2)
      (Algebra.TensorProduct.commRight (Localization.AtPrime p.asIdeal)
        q.asIdeal.ResidueField
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime p.asIdeal)))
  · rintro ⟨_, h⟩
    refine ⟨inferInstance, fun p => ⟨?_, fun q _ => ?_⟩⟩
    · change Module.Flat (Localization.AtPrime p)
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p))
      infer_instance
    · let _ : Algebra q.ResidueField
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p) ⊗[Localization.AtPrime p] q.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      have hg := @Algebra.IsGeometricallyRegular.of_algEquiv _ _ _ _ _ _ _ _
        ((geometricallyRegularProperty_iff _).mp
          (h ⟨p, inferInstance⟩ ⟨q, inferInstance⟩))
        (Algebra.TensorProduct.commRight (Localization.AtPrime p)
          q.ResidueField
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p))).symm
      exact ⟨Algebra.IsGeometricallyRegular.isNoetherianRing hg, hg⟩

/-- A Noetherian ring is a G-ring if and only if every completed localization of a prime
quotient, after base change to the residue field of the smaller prime, is geometrically regular. -/
@[stacks 07PN]
public theorem isGRing_iff_quotientCompletion_isGeometricallyRegular
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ (p q : PrimeSpectrum R) (_hqp : q.asIdeal ≤ p.asIdeal),
        let Q := R ⧸ q.asIdeal
        let S := Localization
          (Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl)
        @Algebra.IsGeometricallyRegular q.asIdeal.ResidueField
          (AdicCompletion
              ((p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)).map (algebraMap Q S)) S ⊗[Q]
            q.asIdeal.ResidueField)
          inferInstance inferInstance Algebra.TensorProduct.rightAlgebra := by
  rw [isGRing_iff_isPRing_geometricallyRegular, propertyRing_iff_quotientCompletion_fibers]
  exact ⟨fun h p q hp ↦ (geometricallyRegularProperty_iff _).mp (h p q hp),
    fun h p q hp ↦ (geometricallyRegularProperty_iff _).mpr (h p q hp)⟩

end

end

/-! ### Quasi-finite ring maps -/

section

section


open IsLocalRing
open scoped TensorProduct

universe u v w x

/-- A geometrically regular algebra over a field is a regular ring. -/
public lemma isRegularRing_of_isGeometricallyRegular
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (h : Algebra.IsGeometricallyRegular k A) : IsRegularRing A :=
  IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k A).toRingEquiv

private lemma geometricallyRegular_includeRight_iff
    {R k A : Type*} [CommRing R] [Field k] [CommRing A] [Algebra R k] [Algebra R A] :
    (letI : Algebra k (A ⊗[R] k) :=
      (Algebra.TensorProduct.includeRight (R := R)).toRingHom.toAlgebra
     Algebra.IsGeometricallyRegular k (A ⊗[R] k)) ↔
      Algebra.IsGeometricallyRegular k (k ⊗[R] A) := by
  let : Algebra k (A ⊗[R] k) :=
    (Algebra.TensorProduct.includeRight (R := R)).toRingHom.toAlgebra
  let e : A ⊗[R] k ≃ₐ[k] k ⊗[R] A :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R A k).toRingEquiv)
      (fun _ => rfl)
  exact ⟨fun h => @Algebra.IsGeometricallyRegular.of_algEquiv _ _ _ _ _ _ _ _ h e,
    fun h => @Algebra.IsGeometricallyRegular.of_algEquiv _ _ _ _ _ _ _ _ h e.symm⟩

private lemma geometricallyRegular_localization_iff
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A] :
    (∀ q : PrimeSpectrum A, Algebra.IsGeometricallyRegular k
      (Localization.AtPrime q.asIdeal)) ↔ Algebra.IsGeometricallyRegular k A := by
  constructor
  · intro h
    constructor
    intro K _ _ _
    let T := K ⊗[k] A
    let : IsNoetherianRing T := Stacks.FormalFibres.isNoetherianRing_tensorProduct_right k K A
    rw [isRegularRing_iff]
    intro p hp
    let q : PrimeSpectrum A :=
      ⟨p.comap (Algebra.TensorProduct.includeRight (R := k)).toRingHom, inferInstance⟩
    let M := q.asIdeal.primeCompl.map (Algebra.TensorProduct.includeRight (R := k) (A := K))
    let L := Localization M
    let e : K ⊗[k] Localization.AtPrime q.asIdeal ≃ₐ[K] L :=
      IsLocalization.tensorProductEquivOfMapIncludeRight k K q.asIdeal.primeCompl
        (Localization.AtPrime q.asIdeal) L
    let : IsRegularRing (K ⊗[k] Localization.AtPrime q.asIdeal) :=
      (h q).isRegularRing_tensorProduct K
    let : IsRegularRing L := IsRegularRing.of_ringEquiv e.toRingEquiv
    have hM : M ≤ p.primeCompl := by
      rintro z ⟨a, ha, rfl⟩
      exact ha
    let : Algebra L (Localization.AtPrime p) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe L (Localization.AtPrime p)
        M p.primeCompl hM
    let : IsScalarTower T L (Localization.AtPrime p) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le L (Localization.AtPrime p)
        M p.primeCompl hM
    let : IsLocalization (p.primeCompl.map (algebraMap T L)) (Localization.AtPrime p) :=
      IsLocalization.isLocalization_of_submonoid_le L (Localization.AtPrime p) M p.primeCompl hM
    let : IsRegularRing (Localization.AtPrime p) :=
      _root_.IsRegularRing.of_isLocalization (p.primeCompl.map (algebraMap T L))
        (Localization.AtPrime p)
    exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  · intro h q
    constructor
    intro K _ _ _
    let M := q.asIdeal.primeCompl.map (Algebra.TensorProduct.includeRight (R := k) (A := K))
    let L := Localization M
    let e : K ⊗[k] Localization.AtPrime q.asIdeal ≃ₐ[K] L :=
      IsLocalization.tensorProductEquivOfMapIncludeRight k K q.asIdeal.primeCompl
        (Localization.AtPrime q.asIdeal) L
    let : IsRegularRing (K ⊗[k] A) := h.isRegularRing_tensorProduct K
    let : IsRegularRing L := _root_.IsRegularRing.of_isLocalization M L
    exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

private lemma geometricallyRegularProperty_algebraMap_iff
    {k A : Type*} [Field k] [CommRing A] [Algebra k A] :
    RingMapProperty.geometricallyRegular (algebraMap k A) ↔
      Algebra.IsGeometricallyRegular k A := by
  rw [RingMapProperty.geometricallyRegular_iff, toAlgebra_algebraMap]

private lemma isPRingAt_geometricallyRegular_iff_isGRing
    (R : Type u) [CommRing R] :
    IsPRingAt.{u, w, x} RingMapProperty.geometricallyRegular R ↔
      IsGRing R := by
  constructor
  · rintro ⟨hN, h⟩
    let : IsNoetherianRing R := hN
    refine ⟨hN, fun p hp ↦ ?_⟩
    rw [isRegularRingHom_algebraMap_iff]
    refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, fun q hq ↦ ?_⟩
    have hg := geometricallyRegular_includeRight_iff.mp
      ((RingMapProperty.geometricallyRegular_holds_iff _).mp
        (h ⟨p, hp⟩ ⟨q, hq⟩))
    let := isRegularRing_of_isGeometricallyRegular hg
    exact ⟨inferInstance, hg⟩
  · rintro ⟨hN, h⟩
    exact ⟨hN, fun p q ↦ (RingMapProperty.geometricallyRegular_holds_iff _).mpr <|
      geometricallyRegular_includeRight_iff.mpr
        ((isRegularRingHom_algebraMap_iff.mp (h p.asIdeal)).2 q.asIdeal).2⟩

/-- Let `R → S` be a finite-type map of Noetherian rings and let `q' ⊆ p'` be primes of
`S` at which the map is quasi-finite at `p'`. Geometric regularity ascends from the corresponding
formal fibre over `R` to that over `S`; it therefore ascends for every formal fibre of the local
rings at the two primes. If the map is quasi-finite everywhere, it also carries the G-ring
property from `R` to `S`. -/
@[stacks 07PP]
public theorem quasiFinite_preserves_geometricallyRegular_formalFibers_and_isGRing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType R S]
    (q' p' : Ideal S) [q'.IsPrime] [p'.IsPrime] (hq'p' : q' ≤ p')
    [Algebra.QuasiFiniteAt R p'] :
    ((let T := AdicCompletion (maximalIdeal (Localization.AtPrime (Ideal.under R p')))
          (Localization.AtPrime (Ideal.under R p')) ⊗[R] (Ideal.under R q').ResidueField
      letI : Algebra (Ideal.under R q').ResidueField T :=
        (Algebra.TensorProduct.includeRight (R := R)).toRingHom.toAlgebra
      Algebra.IsGeometricallyRegular (Ideal.under R q').ResidueField T) →
      (let T := AdicCompletion (maximalIdeal (Localization.AtPrime p'))
          (Localization.AtPrime p') ⊗[S] q'.ResidueField
      letI : Algebra q'.ResidueField T :=
        (Algebra.TensorProduct.includeRight (R := S)).toRingHom.toAlgebra
      Algebra.IsGeometricallyRegular q'.ResidueField T)) ∧
    ((∀ q : PrimeSpectrum (Localization.AtPrime (Ideal.under R p')),
        let T := AdicCompletion (maximalIdeal (Localization.AtPrime (Ideal.under R p')))
            (Localization.AtPrime (Ideal.under R p')) ⊗[Localization.AtPrime (Ideal.under R p')]
          q.asIdeal.ResidueField
        letI : Algebra q.asIdeal.ResidueField T :=
          (Algebra.TensorProduct.includeRight : q.asIdeal.ResidueField →ₐ[
            Localization.AtPrime (Ideal.under R p')] T).toRingHom.toAlgebra
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField T) →
      ∀ q : PrimeSpectrum (Localization.AtPrime p'),
        let T := AdicCompletion (maximalIdeal (Localization.AtPrime p'))
            (Localization.AtPrime p') ⊗[Localization.AtPrime p'] q.asIdeal.ResidueField
        letI : Algebra q.asIdeal.ResidueField T :=
          (Algebra.TensorProduct.includeRight :
            q.asIdeal.ResidueField →ₐ[Localization.AtPrime p'] T).toRingHom.toAlgebra
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField T) ∧
    (Algebra.QuasiFinite R S → IsGRing R → IsGRing S) := by
  have h := quasiFinite_preserves_formalFiberProperty.{u, v, 0, 0}
    RingMapProperty.geometricallyRegular
    (by
      intro k K A _ _ _ _ _ _ _ _ hg
      apply (RingMapProperty.geometricallyRegular_iff _).mpr
      apply geometricallyRegular_includeRight_iff.mpr
      let : Algebra.IsGeometricallyRegular k A :=
        geometricallyRegularProperty_algebraMap_iff.mp hg
      exact Stacks.GeometricallyRegular.SeparableBase.isGeometricallyRegular_tensorProduct k K A)
    (by
      intro k A _ _ _ _
      simp only [geometricallyRegularProperty_algebraMap_iff]
      exact geometricallyRegular_localization_iff k A)
    (R := R) q' p' hq'p'
  refine ⟨?_, ?_, ?_⟩
  · simpa only [RingMapProperty.geometricallyRegular_holds_iff] using h.1
  · simpa only [FormalFibersHaveAt,
      RingMapProperty.geometricallyRegular_holds_iff] using h.2.1
  · exact fun hQ hR ↦ (isPRingAt_geometricallyRegular_iff_isGRing.{v, u, 0} S).mp <|
      h.2.2 hQ ((isPRingAt_geometricallyRegular_iff_isGRing.{u, v, 0} R).mpr hR)

end

end

/-! ### Finite free extensions -/

section

section


open IsLocalRing
open scoped TensorProduct

universe u v w

open Polynomial in
/-- A finite product of regular rings is regular. -/
private theorem isRegularRing_pi {ι : Type*} [Finite ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, IsRegularRing (A i)] : IsRegularRing (∀ i, A i) := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨fun p hp => ?_⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq (⟨p, hp⟩)
  obtain rfl : p = q.asIdeal.comap (Pi.evalRingHom A i) := congrArg PrimeSpectrum.asIdeal hq.symm
  exact IsRegularLocalRing.of_ringEquiv
    (RingEquiv.ofBijective _ (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)).symm

/-- The zero ring is regular. -/
public theorem isRegularRing_of_subsingleton (A : Type*) [CommRing A] [Subsingleton A] :
    IsRegularRing A :=
  ⟨fun _ hp ↦ (hp.ne_top (Subsingleton.elim _ _)).elim⟩

/-- A fibre vanishes if an element of its defining prime becomes a unit in the target. -/
private theorem subsingleton_fiber_of_isUnit {S C : Type*} [CommRing S] [CommRing C]
    [Algebra S C] (q : Ideal S) [q.IsPrime] {x : S} (hx : x ∈ q)
    (hunit : IsUnit (algebraMap S C x)) : Subsingleton (q.Fiber C) := by
  have hu := hunit.map (Algebra.TensorProduct.includeRight (R := S)
    (A := q.ResidueField) (B := C)).toRingHom
  have hz : Algebra.TensorProduct.includeRight (R := S) (A := q.ResidueField)
      (algebraMap S C x) = 0 := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply S q.ResidueField (q.Fiber C),
      Ideal.algebraMap_residueField_eq_zero.mpr hx, map_zero]
  change IsUnit (Algebra.TensorProduct.includeRight (R := S) (A := q.ResidueField)
    (algebraMap S C x)) at hu
  rw [hz] at hu
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

/-- Regularity of formal fibres also holds for pairs of primes that are not comparable: those
fibres vanish. -/
private theorem isRegularRing_formalFiber_of_forall_le
    {S : Type*} [CommRing S]
    (h : ∀ (q p : Ideal S) [q.IsPrime] [p.IsPrime], q ≤ p →
      IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) ⊗[S] q.ResidueField))
    (q p : Ideal S) [q.IsPrime] [p.IsPrime] :
    IsRegularRing (q.ResidueField ⊗[S]
      AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) := by
  classical
  by_cases hqp : q ≤ p
  · have := h q p hqp
    exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm _ _ _).toRingEquiv
  · obtain ⟨x, hx, hxp⟩ := Set.not_subset.mp hqp
    let C := AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)
    have hu : IsUnit (algebraMap S C x) := by
      rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime p) C]
      exact (IsLocalization.map_units (Localization.AtPrime p)
        (⟨x, hxp⟩ : p.primeCompl)).map (algebraMap (Localization.AtPrime p) C)
    have := subsingleton_fiber_of_isUnit q hx hu
    exact isRegularRing_of_subsingleton _

/-- For a finite algebra with regular formal fibres, every residue-field fibre of the base
completion is regular. -/
private theorem isRegularRing_fiber_completion_of_finite
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Module.Finite R S]
    (h : ∀ (q p : Ideal S) [q.IsPrime] [p.IsPrime], q ≤ p →
      IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) ⊗[S] q.ResidueField))
    (q : Ideal S) [q.IsPrime] (p : Ideal R) [p.IsPrime] :
    IsRegularRing (q.ResidueField ⊗[R]
      AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) := by
  classical
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)
  let D (s : p.primesOver S) :=
    AdicCompletion (maximalIdeal (Localization.AtPrime s.1)) (Localization.AtPrime s.1)
  let : Fintype (p.primesOver S) := (Algebra.QuasiFinite.finite_primesOver (S := S) p).fintype
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver
    (R := R) (S := S) p (Localization.AtPrime p) (fun s => Localization.AtPrime s.1)
  have (s : p.primesOver S) : IsRegularRing (q.ResidueField ⊗[S] D s) :=
    isRegularRing_formalFiber_of_forall_le h q s.1
  have := isRegularRing_pi (fun s : p.primesOver S => q.ResidueField ⊗[S] D s)
  let e₁ := Algebra.TensorProduct.cancelBaseChange R S q.ResidueField q.ResidueField C
  let e₂ := Algebra.TensorProduct.congr
    (AlgEquiv.refl : q.ResidueField ≃ₐ[q.ResidueField] q.ResidueField) e
  let e₃ := Algebra.TensorProduct.piRight S q.ResidueField q.ResidueField D
  exact IsRegularRing.of_ringEquiv ((e₁.symm.trans e₂).trans e₃).symm.toRingEquiv

/-- Every finite residue-field extension is realized by a prime in a finite free algebra,
with the algebra allowed to lie in any larger universe. -/
private theorem exists_finiteFree_residueField_algEquiv
    (R : Type u) [CommRing R] (q : Ideal R) [q.IsPrime]
    (L : Type v) [Field L] [Algebra q.ResidueField L] [Module.Finite q.ResidueField L]
    [Algebra R L] [IsScalarTower R q.ResidueField L] :
    ∃ (S : Type (max u w)) (_ : CommRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Module.Free R S)
      (q' : Ideal S) (_ : q'.IsPrime), Nonempty (q'.ResidueField ≃ₐ[R] L) := by
  obtain ⟨S, hS, φ, hff, hq, hcomap, Φ, hΦ⟩ := exists_isFiniteFree_residueField_equiv R q L
  let : Algebra R S := φ.toAlgebra
  obtain ⟨hfree, hfinite⟩ := hff
  let := hfree
  let := hfinite
  let qS := Ideal.map φ q
  let : qS.IsPrime := hq
  let e : qS.ResidueField ≃ₐ[R] L := AlgEquiv.ofRingEquiv (f := Φ) fun r => by
    have hh := DFunLike.congr_fun hΦ (algebraMap R q.ResidueField r)
    have hg := inducedResidueMap_algebraMap φ q qS hcomap r
    change inducedResidueMap φ q qS hcomap (algebraMap R q.ResidueField r) =
      algebraMap R qS.ResidueField r at hg
    rw [RingHom.comp_apply, hg] at hh
    exact hh.trans (IsScalarTower.algebraMap_apply R q.ResidueField L r).symm
  let S' := ULift.{w} S
  let q' : Ideal S' := qS.comap ULift.ringEquiv.toRingHom
  let : q'.IsPrime := Ideal.comap_isPrime _ qS
  let e' : q'.ResidueField ≃ₐ[R] qS.ResidueField :=
    Ideal.residueFieldAlgEquiv q' qS ULift.algEquiv rfl
  exact ⟨S', inferInstance, inferInstance, inferInstance, inferInstance,
    q', inferInstance, ⟨e'.trans e⟩⟩

/-- The finite free criterion implies regularity after any finite residue-field extension. -/
private theorem isRegularRing_tensor_completion_of_finiteFree
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (S : Type (max u v)) [CommRing S] [Algebra R S]
      [Module.Finite R S] [Module.Free R S],
      ∀ (q p : Ideal S) [q.IsPrime] [p.IsPrime], q ≤ p →
        IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p) ⊗[S] q.ResidueField))
    (q p : Ideal R) [q.IsPrime] [p.IsPrime]
    (L : Type w) [Field L] [Algebra q.ResidueField L] [Module.Finite q.ResidueField L]
    [Algebra R L] [IsScalarTower R q.ResidueField L] :
    IsRegularRing (L ⊗[R]
      AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) := by
  obtain ⟨S, hS, aS, hfin, hfree, q', hq', ⟨e⟩⟩ :=
    exists_finiteFree_residueField_algEquiv.{u, w, v} R q L
  have := isRegularRing_fiber_completion_of_finite (h S) q' p
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr e (AlgEquiv.refl)).toRingEquiv

/-- The residue field of a prime of `R` agrees with that of its image in a localization. -/
private theorem bijective_residueField_mapₐ_of_isLocalization
    {R : Type*} [CommRing R] (M : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization M A] (q : Ideal R) [q.IsPrime] (q' : Ideal A) [q'.IsPrime]
    (heq : q = q'.comap (algebraMap R A)) :
    Function.Bijective (Ideal.ResidueField.mapₐ q q' (Algebra.ofId R A) heq) :=
  (RingHom.surjectiveOnStalks_of_isLocalization M A).residueFieldMap_bijective q q' heq

/-- Regularity of `L ⊗[A] C` and of `L ⊗[R] C` agree when `A` is a localization of `R`. -/
private theorem isRegularRing_tensor_iff_of_isLocalization
    {R : Type*} [CommRing R] (M : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization M A] (L C : Type*) [CommRing L] [CommRing C] [Algebra A L] [Algebra R L]
    [IsScalarTower R A L] [Algebra A C] [Algebra R C] [IsScalarTower R A C] :
    IsRegularRing (L ⊗[A] C) ↔ IsRegularRing (L ⊗[R] C) := by
  let : TensorProduct.CompatibleSMul R A L C := IsLocalization.tensorProduct_compatibleSMul M A L C
  let e := Algebra.TensorProduct.equivOfCompatibleSMul R A L L C
  exact ⟨fun h => IsRegularRing.of_ringEquiv e.toRingEquiv,
    fun h => IsRegularRing.of_ringEquiv e.symm.toRingEquiv⟩

/-- Regular formal fibres of all finite free algebras imply the G-ring property. -/
private theorem isGRing_of_finiteFree_formalFibers_isRegularRing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (S : Type (max u v)) [CommRing S] [Algebra R S]
      [Module.Finite R S] [Module.Free R S],
      ∀ (q p : Ideal S) [q.IsPrime] [p.IsPrime], q ≤ p →
        IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p) ⊗[S] q.ResidueField)) : IsGRing R := by
  refine ⟨inferInstance, fun p hp => ?_⟩
  let A := Localization.AtPrime p
  let C := AdicCompletion (maximalIdeal A) A
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨?_, fun q hq => ?_⟩
  · change Module.Flat A C
    infer_instance
  · have hgeo : Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) := by
      constructor
      apply (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
        q.ResidueField (q.Fiber C)).mpr
      intro L _ _ _ _
      let q₀ : Ideal R := q.comap (algebraMap R A)
      let e := AlgEquiv.ofBijective _
        (bijective_residueField_mapₐ_of_isLocalization p.primeCompl A q₀ q rfl)
      have hesurj : Function.Surjective (algebraMap q₀.ResidueField q.ResidueField) :=
        e.surjective
      let : Module.Finite q₀.ResidueField q.ResidueField :=
        Module.Finite.of_surjective
          (Algebra.linearMap q₀.ResidueField q.ResidueField) hesurj
      let : Algebra q₀.ResidueField L :=
        ((algebraMap q.ResidueField L).comp e.toRingHom).toAlgebra
      have : IsScalarTower q₀.ResidueField q.ResidueField L :=
        IsScalarTower.of_algebraMap_eq' rfl
      have : Module.Finite q₀.ResidueField L := Module.Finite.trans q.ResidueField L
      let : Algebra A L :=
        ((algebraMap q.ResidueField L).comp (algebraMap A q.ResidueField)).toAlgebra
      have : IsScalarTower A q.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
      let : Algebra R L := ((algebraMap A L).comp (algebraMap R A)).toAlgebra
      have : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq' rfl
      have : IsScalarTower R q₀.ResidueField L := by
        apply IsScalarTower.of_algebraMap_eq
        intro r
        change algebraMap q.ResidueField L (algebraMap A q.ResidueField (algebraMap R A r)) =
          algebraMap q.ResidueField L (e (algebraMap R q₀.ResidueField r))
        rw [e.commutes, IsScalarTower.algebraMap_apply R A q.ResidueField]
      have := isRegularRing_tensor_completion_of_finiteFree R h q₀ p L
      have hr := (isRegularRing_tensor_iff_of_isLocalization p.primeCompl A L C).mpr this
      exact IsRegularRing.of_ringEquiv
        (Algebra.TensorProduct.cancelBaseChange A q.ResidueField L L C).symm.toRingEquiv
    have := isRegularRing_of_isGeometricallyRegular hgeo
    exact ⟨inferInstance, hgeo⟩

/-- The formal fibre associated to a pair of comparable primes of a G-ring is regular. -/
private theorem isRegularRing_formalFiber_of_isGRing
    {R : Type u} [CommRing R] (hR : IsGRing R)
    (q p : Ideal R) [q.IsPrime] [p.IsPrime] (hqp : q ≤ p) :
    IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p) ⊗[R] q.ResidueField) := by
  let A := Localization.AtPrime p
  let C := AdicCompletion (maximalIdeal A) A
  have hdis : Disjoint (p.primeCompl : Set R) (q : Set R) :=
    Set.disjoint_left.mpr fun x hx hqx => hx (hqp hqx)
  let q' : Ideal A := q.map (algebraMap R A)
  have : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl A q
    inferInstance hdis
  have heq : q = q'.comap (algebraMap R A) :=
    (IsLocalization.under_map_of_isPrime_disjoint p.primeCompl A inferInstance hdis).symm
  let e := AlgEquiv.ofBijective _
    (bijective_residueField_mapₐ_of_isLocalization p.primeCompl A q q' heq)
  have hg := (isRegularRingHom_algebraMap_iff.mp (hR.2 p)).2 q'
  have := isRegularRing_of_isGeometricallyRegular hg.2
  have : IsRegularRing (q'.ResidueField ⊗[R] C) :=
    (isRegularRing_tensor_iff_of_isLocalization p.primeCompl A q'.ResidueField C).mp this
  have : IsRegularRing (q.ResidueField ⊗[R] C) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl : C ≃ₐ[R] C)).toRingEquiv
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm R q.ResidueField C).toRingEquiv

/-- A Noetherian ring is a G-ring if and only if every formal fibre of every finite free algebra
over it is a regular ring. -/
@[stacks 07PQ]
public theorem isGRing_iff_finiteFree_formalFibers_isRegularRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] [Module.Finite R S]
          [Module.Free R S],
        ∀ (q p : Ideal S) [q.IsPrime] [p.IsPrime], q ≤ p →
          IsRegularRing
            (AdicCompletion (maximalIdeal (Localization.AtPrime p))
                (Localization.AtPrime p) ⊗[S] q.ResidueField) := by
  constructor
  · intro hR S _ _ _ _ q p _ _ hqp
    have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
    have hS := (quasiFinite_preserves_geometricallyRegular_formalFibers_and_isGRing
      (R := R) q p hqp).2.2 inferInstance hR
    exact isRegularRing_formalFiber_of_isGRing hS q p hqp
  · exact isGRing_of_finiteFree_formalFibers_isRegularRing R

end

end

/-! ### Formal fibres of polynomial rings over power-series rings -/

section

section


open IsLocalRing
open scoped TensorProduct Pointwise

universe u v w

attribute [local instance 2000] Ring.toIntAlgebra

private theorem exists_derivation_formalFiber_extends
    {B : Type*} [CommRing B] (q : Ideal B) [q.IsPrime]
    (M : Type*) [Field M] [Algebra B M] [IsFractionRing B M]
    (D : Derivation ℤ B B) :
    ∃ E : Derivation ℤ
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q) ⊗[B] M)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q) ⊗[B] M),
      Stacks.DerivationExtension.ExtendsAlong
        (algebraMap B (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q) ⊗[B] M)) D E := by
  let Q := Localization.AtPrime q
  let C := AdicCompletion (maximalIdeal Q) Q
  let T := C ⊗[B] M
  let Dq : Derivation ℤ Q Q := Stacks.DerivationExtension.locDeriv D q.primeCompl Q
  have hDq : Stacks.DerivationExtension.ExtendsAlong (algebraMap B Q) D Dq :=
    Stacks.DerivationExtension.locDeriv_extendsAlong D q.primeCompl Q
  obtain ⟨Dc, hDc⟩ :=
    Stacks.DerivationExtension.exists_derivation_adicCompletion Q Dq (maximalIdeal Q)
  let E : Derivation ℤ T T :=
    Stacks.DerivationExtension.locDeriv Dc (Algebra.algebraMapSubmonoid C (nonZeroDivisors B)) T
  have hE : Stacks.DerivationExtension.ExtendsAlong (algebraMap C T) Dc E :=
    Stacks.DerivationExtension.locDeriv_extendsAlong Dc (Algebra.algebraMapSubmonoid C
      (nonZeroDivisors B)) T
  refine ⟨E, fun b => ?_⟩
  rw [IsScalarTower.algebraMap_apply B C T, hE,
    IsScalarTower.algebraMap_apply B Q C, hDc, hDq,
    ← IsScalarTower.algebraMap_apply B Q C]
  exact (IsScalarTower.algebraMap_apply B C T (D b)).symm

private theorem exists_derivation_formalFiber_isUnit
    {B : Type*} [CommRing B] [IsDomain B] (q : Ideal B) [q.IsPrime]
    (M : Type*) [Field M] [Algebra B M] [IsFractionRing B M]
    (D : Derivation ℤ B B) (f : B) (hf : D f ≠ 0) :
    ∃ E : Derivation ℤ
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q) ⊗[B] M)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q) ⊗[B] M),
      IsUnit (E (algebraMap B _ f)) := by
  obtain ⟨E, hE⟩ := exists_derivation_formalFiber_extends q M D
  refine ⟨E, ?_⟩
  rw [hE]
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
  have hne : algebraMap B M (D f) ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective B M).ne hf
  have hu := (isUnit_iff_ne_zero.mpr hne).map
    (Algebra.TensorProduct.includeRight : M →ₐ[B] C ⊗[B] M)
  rwa [AlgHom.commutes] at hu

private theorem isAdicComplete_maximalIdeal_mvPowerSeries
    (k : Type*) [Field k] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) k)) (MvPowerSeries (Fin n) k) := by
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X]
  infer_instance

private theorem isRegularRing_of_isRegularLocalRing (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsRegularRing R :=
  ((IsLocalRing.isRegularRing_tfae (R := R)).out 1 3).mp (inferInstance : IsRegularLocalRing R)

private theorem isRegularRing_formalFiber
    {A : Type*} [CommRing A] [IsRegularRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (q : Ideal A) [q.IsPrime] :
    IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) ⊗[A] K) := by
  let Q := Localization.AtPrime q
  let C := AdicCompletion (maximalIdeal Q) Q
  have : IsRegularLocalRing C :=
    isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp inferInstance
  have : IsRegularRing C := isRegularRing_of_isRegularLocalRing C
  exact _root_.IsRegularRing.of_isLocalization
    (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) _

private theorem subsingleton_primesOver_of_pow_mem
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hpow : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ (algebraMap A B).range)
    (q : Ideal A) : Subsingleton (q.primesOver B) := by
  refine ⟨fun r s => Subtype.ext (Ideal.ext fun b => ?_)⟩
  obtain ⟨n, hn, a, ha⟩ := hpow b
  have hcomap : r.1.comap (algebraMap A B) = s.1.comap (algebraMap A B) :=
    (Ideal.LiesOver.over (P := r.1) (p := q)).symm.trans
      (Ideal.LiesOver.over (P := s.1) (p := q))
  rw [← (Ideal.primesOver.isPrime q r).pow_mem_iff_mem n hn,
    ← (Ideal.primesOver.isPrime q s).pow_mem_iff_mem n hn, ← ha]
  exact SetLike.ext_iff.mp hcomap a

private theorem pow_mem_range_of_isIntegral_of_isPurelyInseparable
    {A B K L : Type*} [CommRing A] [CommRing B] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A B] [Algebra.IsIntegral A B]
    [Algebra A K] [IsFractionRing A K] [Algebra A L] [Algebra K L]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L]
    [FaithfulSMul B L] [IsPurelyInseparable K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] (b : B) :
    ∃ n : ℕ, b ^ p ^ n ∈ (algebraMap A B).range := by
  obtain ⟨n, x, hx⟩ := IsPurelyInseparable.pow_mem K p (algebraMap B L b)
  have hxint : IsIntegral A x := by
    apply (isIntegral_algebraMap_iff (B := L)).mp
    rw [hx]
    exact ((Algebra.IsIntegral.isIntegral b).algebraMap (B := L)).pow _
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxint
  refine ⟨n, a, ?_⟩
  apply FaithfulSMul.algebraMap_injective B L
  rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L,
    ha, hx, map_pow]

private theorem subsingleton_primesOver_of_isPurelyInseparable
    {A B K M : Type*} [CommRing A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field M] [Algebra A M] [Algebra B M] [Algebra K M]
    [IsScalarTower A B M] [IsScalarTower A K M] [FaithfulSMul B M]
    [IsPurelyInseparable K M] (p : ℕ) [Fact p.Prime] [CharP K p] (q : Ideal A) :
    Subsingleton (q.primesOver B) :=
  subsingleton_primesOver_of_pow_mem
    (fun b => by
      obtain ⟨n, hn⟩ := pow_mem_range_of_isIntegral_of_isPurelyInseparable
        (A := A) (B := B) (K := K) (L := M) p b
      exact ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, hn⟩) q

private theorem nonempty_ringEquiv_formalFiber_of_subsingleton_primesOver
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B]
    (q : Ideal A) [q.IsPrime] [Subsingleton (q.primesOver B)] (r : q.primesOver B)
    (M : Type*) [CommRing M] [Algebra A M] [Algebra B M] [IsScalarTower A B M] :
    Nonempty
      ((AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) ⊗[A] M)
        ≃+* (AdicCompletion (maximalIdeal (Localization.AtPrime r.1))
          (Localization.AtPrime r.1) ⊗[B] M)) := by
  classical
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
  let F := fun s : q.primesOver B =>
    AdicCompletion (maximalIdeal (Localization.AtPrime s.1)) (Localization.AtPrime s.1)
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver (S := B)
    q (Localization.AtPrime q) (fun s => Localization.AtPrime s.1)
  have heval : Function.Bijective (Pi.evalAlgHom B F r) := by
    refine ⟨fun x y h ↦ funext fun s ↦ ?_, fun x => ⟨Pi.single r x, by simp⟩⟩
    obtain rfl : s = r := Subsingleton.elim _ _
    exact h
  let e' : B ⊗[A] C ≃ₐ[B] F r := e.trans (AlgEquiv.ofBijective _ heval)
  let eM := Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[B] M) e'
  exact ⟨(Algebra.TensorProduct.comm A C M).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange A B B M C).symm.toRingEquiv.trans
      (eM.toRingEquiv.trans (Algebra.TensorProduct.comm B M (F r)).toRingEquiv))⟩

private theorem exists_ringEquiv_formalFiber_of_isPurelyInseparable
    {A B K M : Type*} [CommRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field M] [Algebra A M] [Algebra B M] [Algebra K M]
    [IsScalarTower A B M] [IsScalarTower A K M] [FaithfulSMul B M]
    [IsPurelyInseparable K M] (p : ℕ) [Fact p.Prime] [CharP K p]
    (q : Ideal A) [q.IsPrime] :
    ∃ r : q.primesOver B, Nonempty
      ((AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) ⊗[A] M)
        ≃+* (AdicCompletion (maximalIdeal (Localization.AtPrime r.1))
          (Localization.AtPrime r.1) ⊗[B] M)) := by
  have := subsingleton_primesOver_of_isPurelyInseparable (B := B) (K := K) (M := M) p q
  obtain ⟨r⟩ := (inferInstance : Nonempty (q.primesOver B))
  exact ⟨r, nonempty_ringEquiv_formalFiber_of_subsingleton_primesOver q r M⟩

private theorem nonempty_algEquiv_tensor_adjoinRoot
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (P : Polynomial R) :
    Nonempty (T ⊗[R] AdjoinRoot P ≃ₐ[T] AdjoinRoot (P.map (algebraMap R T))) :=
  ⟨(AdjoinRoot.tensorAlgEquiv P
    (P.map (Algebra.TensorProduct.includeRight : R →ₐ[R] T ⊗[R] R)) rfl).trans
      (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R T T) _ _ (by
        apply Associated.of_eq
        rw [Polynomial.map_map]
        congr 1
        ext r
        simp [Algebra.smul_def]))⟩

private theorem isRegularRing_tensor_adjoinRoot_of_isUnit_derivation
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] [IsRegularRing T]
    (f : R) (D : Derivation ℤ T T) (hD : IsUnit (D (algebraMap R T f))) (n : ℕ) :
    IsRegularRing (T ⊗[R] AdjoinRoot (Polynomial.X ^ n - Polynomial.C f)) := by
  have hreg := isRegularRing_quotient_polynomial_sub_C_of_isUnit_derivation
    (algebraMap R T f) D hD ((Polynomial.X : Polynomial ℤ) ^ n)
  have : IsRegularRing (AdjoinRoot
      ((Polynomial.X ^ n - Polynomial.C f).map (algebraMap R T))) := by
    change IsRegularRing (Polynomial T ⧸ Ideal.span
      {(Polynomial.X ^ n - Polynomial.C f).map (algebraMap R T)})
    have hP : (Polynomial.X ^ n - Polynomial.C f).map (algebraMap R T) =
        (Polynomial.X : Polynomial T) ^ n - Polynomial.C (algebraMap R T f) := by simp
    have hZ : ((Polynomial.X : Polynomial ℤ) ^ n).map (algebraMap ℤ T) =
        (Polynomial.X : Polynomial T) ^ n := by simp
    rw [hP]
    rwa [hZ] at hreg
  obtain ⟨e⟩ := nonempty_algEquiv_tensor_adjoinRoot (T := T) (Polynomial.X ^ n - Polynomial.C f)
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

private theorem exists_derivation_ringEquiv_extends
    {R S : Type*} [CommRing R] [CommRing S] (D : Derivation ℤ R R) (e : R ≃+* S) :
    ∃ E : Derivation ℤ S S, Stacks.DerivationExtension.ExtendsAlong e.toRingHom D E := by
  let E := e.toIntAlgEquiv
  let F := E.toLinearMap.comp (D.toLinearMap.comp E.symm.toLinearMap)
  have hF : ∀ x y, F (x * y) = x • F y + y • F x := by
    intro x y
    change e (D (e.symm (x * y))) = x * e (D (e.symm y)) + y * e (D (e.symm x))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, e.apply_symm_apply]
  refine ⟨Derivation.mk' F hF, fun x => ?_⟩
  change e (D (e.symm (e x))) = e (D x)
  rw [e.symm_apply_apply]

private theorem isRegularRing_formalFiber_adjoinRoot
    {p : ℕ} [Fact p.Prime] {R B M : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing B] [IsDomain B] [CharP B p] [Algebra R B] [Algebra.FiniteType R B]
    [Field M] [Algebra B M] [IsFractionRing B M]
    (q : Ideal B) [q.IsPrime] (f : B)
    (hf : ¬ ∃ x : M, algebraMap B M f = x ^ p)
    (hreg : IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) ⊗[B] M)) :
    IsRegularRing ((M ⊗[B] AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)) ⊗[M]
        AdjoinRoot (Polynomial.X ^ p - Polynomial.C (algebraMap B M f))) := by
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
  let e := Algebra.TensorProduct.comm B C M
  have : IsRegularRing (C ⊗[B] M) := hreg
  have : IsRegularRing (M ⊗[B] C) := IsRegularRing.of_ringEquiv e.toRingEquiv
  obtain ⟨D, hD⟩ :=
    exists_derivation_apply_ne_zero_of_not_pow_fractionRing (R := R) f hf
  obtain ⟨E, hE⟩ := exists_derivation_formalFiber_isUnit q M D f hD
  obtain ⟨E', hE'⟩ := exists_derivation_ringEquiv_extends E e.toRingEquiv
  apply isRegularRing_tensor_adjoinRoot_of_isUnit_derivation (D := E')
  have he : algebraMap M (M ⊗[B] C) (algebraMap B M f) = e (algebraMap B (C ⊗[B] M) f) := by
    rw [AlgEquiv.commutes]
    exact (IsScalarTower.algebraMap_apply B M (M ⊗[B] C) f).symm
  rw [he, show E' (e (algebraMap B (C ⊗[B] M) f)) =
      e (E (algebraMap B (C ⊗[B] M) f)) from hE' _]
  exact hE.map e.toRingHom

private theorem isRegularRing_formalFiber_of_adjoinRoot_algEquiv
    {p : ℕ} [Fact p.Prime] {R B M L : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing B] [IsDomain B] [CharP B p] [Algebra R B] [Algebra.FiniteType R B]
    [Field M] [Algebra B M] [IsFractionRing B M]
    [CommRing L] [Algebra B L] [Algebra M L] [IsScalarTower B M L]
    (q : Ideal B) [q.IsPrime] (f : B)
    (hf : ¬ ∃ x : M, algebraMap B M f = x ^ p)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C (algebraMap B M f)) ≃ₐ[M] L)
    (hreg : IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) ⊗[B] M)) :
    IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) ⊗[B] L) := by
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
  let T := M ⊗[B] C
  have : IsRegularRing (T ⊗[M]
      AdjoinRoot (Polynomial.X ^ p - Polynomial.C (algebraMap B M f))) :=
    isRegularRing_formalFiber_adjoinRoot (R := R) q f hf hreg
  have : IsRegularRing (T ⊗[M] L) := IsRegularRing.of_ringEquiv
    (R := T ⊗[M] AdjoinRoot (Polynomial.X ^ p - Polynomial.C (algebraMap B M f)))
    (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[M] T) e).toRingEquiv
  exact IsRegularRing.of_ringEquiv (R := T ⊗[M] L)
    ((Algebra.TensorProduct.comm M T L).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange B M M L C).toRingEquiv.trans
        (Algebra.TensorProduct.comm B L C).toRingEquiv))

private theorem isGeometricallyRegular_formalFiber_of_finite_isPurelyInseparable
    {A : Type*} {K : Type u} [CommRing A] [Field K] [Algebra A K]
    (q : Ideal A) [q.IsPrime]
    (h : ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
      [IsPurelyInseparable K L],
      letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
      IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q) ⊗[A] L)) :
    let T := AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) ⊗[A] K
    letI : Algebra K T :=
      (Algebra.TensorProduct.includeRight : K →ₐ[A] T).toRingHom.toAlgebra
    Algebra.IsGeometricallyRegular K T := by
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
  let T := C ⊗[A] K
  let : Algebra K T :=
    (Algebra.TensorProduct.includeRight : K →ₐ[A] T).toRingHom.toAlgebra
  let e : T ≃ₐ[K] K ⊗[A] C :=
    { (Algebra.TensorProduct.comm A C K).toRingEquiv with
      commutes' := fun k => by
        change (Algebra.TensorProduct.comm A C K) (1 ⊗ₜ[A] k) = k ⊗ₜ[A] 1
        exact Algebra.TensorProduct.comm_tmul A 1 k }
  constructor
  apply (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    K T).mpr
  intro L _ _ _ _
  let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsRegularRing (C ⊗[A] L) := h L
  let eL : L ⊗[K] T ≃+* C ⊗[A] L :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) e).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange A K K L C).toRingEquiv.trans
        (Algebra.TensorProduct.comm A L C).toRingEquiv)
  exact IsRegularRing.of_ringEquiv (R := C ⊗[A] L) eL.symm

private theorem exists_mul_pow_eq_algebraMap_of_not_pow
    {B M : Type*} [CommRing B] [IsDomain B] [Field M] [Algebra B M] [IsFractionRing B M]
    (p : ℕ) (hp : 0 < p) (f : M) (hf : ¬ ∃ x : M, f = x ^ p) :
    ∃ d b : B, d ≠ 0 ∧ algebraMap B M d ^ p * f = algebraMap B M b ∧
      ¬ ∃ x : M, algebraMap B M b = x ^ p := by
  obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors B) f
  have hd0 : (d : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hdm : algebraMap B M d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B M).ne hd0
  let b := a * (d : B) ^ (p - 1)
  have hb : algebraMap B M d ^ p * f = algebraMap B M b := by
    dsimp [b]
    rw [map_mul, map_pow, ← hd]
    conv_lhs => rw [← Nat.sub_add_cancel hp, pow_succ]
    ring
  refine ⟨d, b, hd0, hb, ?_⟩
  rintro ⟨x, hx⟩
  refine hf ⟨x / algebraMap B M d, ?_⟩
  rw [div_pow, eq_div_iff (pow_ne_zero _ hdm), mul_comm, hb, hx]

private theorem nonempty_adjoinRoot_algEquiv_of_primitive_pow
    {M N : Type*} [Field M] [Field N] [Algebra M N]
    {p : ℕ} [Fact p.Prime] (x : N) (f : M)
    (hf : ¬ ∃ y : M, f = y ^ p)
    (hx : x ^ p = algebraMap M N f) (hgen : IntermediateField.adjoin M {x} = ⊤) :
    Nonempty (AdjoinRoot (Polynomial.X ^ p - Polynomial.C f) ≃ₐ[M] N) := by
  have hirr := X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime)
    (fun y h => hf ⟨y, h.symm⟩)
  have heval : Polynomial.aeval x (Polynomial.X ^ p - Polynomial.C f) = 0 := by
    simp [hx]
  have heq := minpoly.eq_of_irreducible_of_monic hirr heval
    (Polynomial.monic_X_pow_sub_C f (Fact.out : p.Prime).ne_zero)
  have hint : IsIntegral M x := ⟨_, Polynomial.monic_X_pow_sub_C f
    (Fact.out : p.Prime).ne_zero, heval⟩
  rw [heq]
  exact ⟨(IsAdjoinRoot.mkOfPrimitiveElement hint hgen).adjoinRootAlgEquiv⟩

private theorem isRegularRing_formalFiber_of_primitive_pow
    {R A K M N : Type*} {p : ℕ} [Fact p.Prime]
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra R A] [Algebra.FiniteType R A]
    [Field K] [Algebra A K] [IsFractionRing A K] [CharP K p]
    [Field M] [Algebra A M] [Algebra K M] [IsScalarTower A K M]
    [Module.Finite K M] [IsPurelyInseparable K M]
    [Field N] [Algebra A N] [Algebra M N] [IsScalarTower A M N]
    (q : Ideal A) [q.IsPrime] (x : N) (f : M)
    (hf : ¬ ∃ y : M, f = y ^ p)
    (hx : x ^ p = algebraMap M N f) (hgen : IntermediateField.adjoin M {x} = ⊤)
    (hreg : IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) ⊗[A] M)) :
    IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) ⊗[A] N) := by
  classical
  obtain ⟨B, hBfin, hBfrac⟩ := Algebra.exists_finite_subalgebra_isFractionRing A K M
  have : Module.Finite A B := hBfin
  have : IsFractionRing B M := hBfrac
  let : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R A) (inferInstance : Algebra.FiniteType A B)
  have : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
  have : CharP B p := ((algebraMap B M).charP_iff (IsFractionRing.injective B M) p).mpr
    inferInstance
  have hAM : Function.Injective (algebraMap A M) := by
    rw [IsScalarTower.algebraMap_eq A K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (fun a b h => hAM (by simpa using congrArg (algebraMap B M) h))
  obtain ⟨r, ⟨eM⟩⟩ := exists_ringEquiv_formalFiber_of_isPurelyInseparable
    (B := B) (K := K) (M := M) p q
  have := subsingleton_primesOver_of_isPurelyInseparable (B := B) (K := K) (M := M) p q
  obtain ⟨eN⟩ := nonempty_ringEquiv_formalFiber_of_subsingleton_primesOver q r N
  have : IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q) ⊗[A] M) := hreg
  have hregB := IsRegularRing.of_ringEquiv (R := AdicCompletion
    (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) ⊗[A] M) eM
  obtain ⟨d, b, hd, hb, hbp⟩ := exists_mul_pow_eq_algebraMap_of_not_pow
    (B := B) p (Fact.out : p.Prime).pos f hf
  have hdM : algebraMap B M d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B M).ne hd
  let y := x * algebraMap M N (algebraMap B M d)
  have hy : y ^ p = algebraMap M N (algebraMap B M b) := by
    rw [show y = x * algebraMap M N (algebraMap B M d) from rfl, mul_pow, hx,
      ← map_pow, ← map_mul, mul_comm, hb]
  have hygen : IntermediateField.adjoin M {y} = ⊤ := by
    apply top_unique
    rw [← hgen, IntermediateField.adjoin_simple_le_iff]
    have hy_mem := IntermediateField.subset_adjoin M {y} (Set.mem_singleton y)
    have heq : x = y * algebraMap M N (algebraMap B M d)⁻¹ := by
      have hdN : algebraMap M N (algebraMap B M d) ≠ 0 := by
        simpa only [map_zero] using (algebraMap M N).injective.ne hdM
      dsimp only [y]
      rw [map_inv₀, mul_assoc, mul_inv_cancel₀ hdN, mul_one]
    rw [heq]
    exact (IntermediateField.adjoin M {y}).mul_mem hy_mem
      ((IntermediateField.adjoin M {y}).algebraMap_mem _)
  obtain ⟨e⟩ := nonempty_adjoinRoot_algEquiv_of_primitive_pow y _ hbp hy hygen
  have hregN := isRegularRing_formalFiber_of_adjoinRoot_algEquiv
    (R := R) r.1 b hbp e hregB
  exact IsRegularRing.of_ringEquiv eN.symm

private theorem intermediateField_induction_of_pth_root
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [IsPurelyInseparable K L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : IntermediateField K L → Prop) (hbot : P ⊥)
    (hstep : ∀ (F : IntermediateField K L) (x : L), x ∉ F → x ^ p ∈ F →
      P F → P ((IntermediateField.adjoin F {x}).restrictScalars K)) : P ⊤ := by
  classical
  have aux : ∀ n (F : IntermediateField K L), Module.finrank F L = n → P F → P ⊤ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F hn hF
      by_cases htop : F = ⊤
      · simpa [htop] using hF
      obtain ⟨x, hx⟩ : ∃ x : L, x ∉ F := by
        simpa only [eq_top_iff, IsConcreteLE.le_iff, IntermediateField.mem_top,
          true_implies, not_forall] using htop
      obtain ⟨m, hm⟩ := IsPurelyInseparable.pow_mem F p x
      replace hm : x ^ p ^ m ∈ F := by
        obtain ⟨a, ha⟩ := hm
        exact ha ▸ a.property
      let j := Nat.find (show ∃ j, x ^ p ^ j ∈ F from ⟨m, hm⟩)
      have hj : x ^ p ^ j ∈ F := Nat.find_spec (show ∃ j, x ^ p ^ j ∈ F from ⟨m, hm⟩)
      have hjmin (i) : x ^ p ^ i ∈ F → j ≤ i :=
        Nat.find_min' (p := fun i => x ^ p ^ i ∈ F) ⟨m, hm⟩
      have hj0 : j ≠ 0 := fun h => by simp [h, hx] at hj
      let y := x ^ p ^ (j - 1)
      have hy : y ∉ F := by
        intro h
        have := hjmin (j - 1) h
        omega
      have hyp : y ^ p ∈ F := by
        dsimp [y]
        rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
        exact hj
      let E := IntermediateField.adjoin F {y}
      have hFE : Module.finrank F E ≠ 1 :=
        IntermediateField.bot_eq_top_iff_finrank_eq_one.not.mp <| by
          simpa [E, eq_top_iff, IsConcreteLE.le_iff,
            IntermediateField.mem_bot, Subtype.ext_iff]
            using ⟨y, IntermediateField.subset_adjoin F {y} (by simp), hy⟩
      have hlt : Module.finrank E L < n := by
        rw [← hn, ← Module.finrank_mul_finrank F E L]
        apply (lt_mul_iff_one_lt_left Module.finrank_pos).mpr
        have := Module.finrank_pos (R := F) (M := E)
        omega
      exact ih _ hlt (E.restrictScalars K) rfl (hstep F y hy hyp hF)
  exact aux _ ⊥ rfl hbot

private theorem isRegularRing_formalFiber_finite_isPurelyInseparable
    {R A K L : Type*} {p : ℕ} [Fact p.Prime]
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing A] [IsDomain A] [IsRegularRing A] [IsIntegrallyClosed A]
    [Algebra R A] [Algebra.FiniteType R A]
    [Field K] [Algebra A K] [IsFractionRing A K] [CharP K p]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [Module.Finite K L] [IsPurelyInseparable K L]
    (q : Ideal A) [q.IsPrime] :
    IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) ⊗[A] L) := by
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
  let P (F : IntermediateField K L) := IsRegularRing (C ⊗[A] F)
  have hbot : P ⊥ := by
    have : IsRegularRing (C ⊗[A] K) := isRegularRing_formalFiber K q
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[A] C)
        ((IntermediateField.botEquiv K L).symm.restrictScalars A)).toRingEquiv
  have htop : P ⊤ := intermediateField_induction_of_pth_root K L p P hbot (by
    intro F x hx hxp hF
    have : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let E := IntermediateField.adjoin F {x}
    let : Algebra A E := IntermediateField.algebra' E
    have : IsScalarTower A F E := E.isScalarTower
    let y : E := IntermediateField.AdjoinSimple.gen F x
    let f : F := ⟨x ^ p, hxp⟩
    have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    have hf : ¬ ∃ z : F, f = z ^ p := by
      rintro ⟨z, hz⟩
      have hp : x ^ p = (z : L) ^ p := congrArg (fun t : F => (t : L)) hz
      have heq : x = (z : L) := frobenius_inj L p hp
      exact hx (heq ▸ z.property)
    have hy : y ^ p = algebraMap F E f := (algebraMap E L).injective rfl
    have hgen : IntermediateField.adjoin F {y} = ⊤ := by
      apply IntermediateField.adjoin_eq_top_of_algebra
      simpa only [IntermediateField.adjoin.powerBasis_gen] using
        (IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral x)).adjoin_gen_eq_top
    change IsRegularRing (C ⊗[A] E)
    exact isRegularRing_formalFiber_of_primitive_pow (R := R) (K := K) q y f hf hy hgen hF)
  have : IsRegularRing (C ⊗[A] (⊤ : IntermediateField K L)) := htop
  let eTop :=
    (IntermediateField.topEquiv : (⊤ : IntermediateField K L) ≃ₐ[K] L).restrictScalars A
  exact IsRegularRing.of_ringEquiv (R := C ⊗[A] (⊤ : IntermediateField K L))
    (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[A] C) eTop).toRingEquiv

/-- If `A` is a polynomial ring in `m` variables over the formal power-series
ring in `n` variables over a field `k` of prime characteristic, then the generic formal fibre of
the completion of `A` at any prime ideal is geometrically regular over the fraction field of
`A`. -/
@[stacks 07PR, ega "0 22.3.4" "special case"]
public theorem
    isGeometricallyRegular_formalFiber_mvPolynomial_mvPowerSeries
    {p m n : ℕ} [Fact p.Prime] (k : Type u) (A : Type v) (K : Type w) [Field k] [CharP k p]
    [CommRing A] [Algebra k A]
    (_ : A ≃ₐ[k] MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))
    [Field K] [Algebra A K] [IsFractionRing A K]
    (q : Ideal A) [q.IsPrime] :
    let T := AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q) ⊗[A] K
    letI : Algebra K T :=
      (Algebra.TensorProduct.includeRight : K →ₐ[A] T).toRingHom.toAlgebra
    Algebra.IsGeometricallyRegular K T := by
  let e := ‹A ≃ₐ[k] MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)›
  let R := MvPowerSeries (Fin n) k
  let S := MvPolynomial (Fin m) R
  have : IsDomain R := NoZeroDivisors.to_isDomain _
  have : IsDomain S := inferInstance
  have : IsDomain A := Function.Injective.isDomain e.toRingEquiv e.injective
  have : IsIntegrallyClosed R :=
    Stacks.FieldTheory.PBasisDifferentials.isIntegrallyClosed_mvPowerSeries k n
  have : IsIntegrallyClosed S :=
    Stacks.FieldTheory.PBasisDifferentials.isIntegrallyClosed_mvPolynomial R m
  have : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.symm.toRingEquiv
  have : IsRegularLocalRing R := MvPowerSeries.isRegularLocalRing k n
  have : IsRegularRing R := isRegularRing_of_isRegularLocalRing R
  have : IsRegularRing A := IsRegularRing.of_ringEquiv e.symm.toRingEquiv
  have : IsAdicComplete (maximalIdeal R) R := isAdicComplete_maximalIdeal_mvPowerSeries k n
  let : Algebra R A := (e.symm.toRingHom.comp (algebraMap R S)).toAlgebra
  let eR : S ≃ₐ[R] A := { e.symm.toRingEquiv with commutes' := fun _ => rfl }
  have : Algebra.FiniteType R A := Algebra.FiniteType.of_surjective eR.toAlgHom eR.surjective
  have : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  have : CharP K p := IsFractionRing.charP_of_isFractionRing A p
  apply isGeometricallyRegular_formalFiber_of_finite_isPurelyInseparable
  intro L _ _ _ _
  let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact isRegularRing_formalFiber_finite_isPurelyInseparable (R := R) (K := K) (p := p) q

end

end

/-! ### Complete local rings -/

section

section


open IsLocalRing
open scoped TensorProduct

universe u v w

namespace Stacks.GRing

/-- A regular ring over a perfect field is geometrically regular. -/
public theorem isGeometricallyRegular_of_perfectField (k : Type u) (A : Type v)
    [Field k] [PerfectField k] [CommRing A] [Algebra k A] [IsRegularRing A] :
    Algebra.IsGeometricallyRegular k A := by
  constructor
  apply (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    k A).mpr
  intro K _ _ _ _
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K)
    (IsPurelyInseparable.bijective_algebraMap_of_isSeparable k K)
  exact IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.lid k A).symm.trans
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[k] A))).toRingEquiv

end Stacks.GRing

private theorem isGeometricallyRegular_genericFormalFiber_of_perfectField
    (A : Type u) (K : Type v) [CommRing A] [IsRegularRing A]
    [Field K] [PerfectField K] [Algebra A K] [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime] :
    let T := AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p) ⊗[A] K
    letI : Algebra K T := Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyRegular K T := by
  let : Algebra K (AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p) ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
  have := isRegularRing_formalFiber K p
  exact Stacks.GRing.isGeometricallyRegular_of_perfectField K _

private theorem isPrecomplete_maximalIdeal_of_surjective {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [IsPrecomplete (maximalIdeal R) R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) : IsPrecomplete (maximalIdeal S) S := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) h,
    IsPrecomplete.map_algebraMap_iff, ← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨x, rfl⟩ := AdicCompletion.map_surjective (maximalIdeal R)
    (f := Algebra.linearMap R S) h y
  obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective (I := maximalIdeal R) (M := R) x
  exact ⟨algebraMap R S r,
    (AdicCompletion.map_of (maximalIdeal R) (Algebra.linearMap R S) r).symm⟩

/-- Geometric regularity over a field is invariant under algebra isomorphisms. -/
public theorem isGeometricallyRegular_of_algEquiv
    {k : Type u} {A : Type v} {B : Type w} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (h : Algebra.IsGeometricallyRegular k A) : Algebra.IsGeometricallyRegular k B := by
  constructor
  intro K _ _ _
  have := h.isRegularRing_tensorProduct K
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[k] K) e).toRingEquiv

private theorem isGeometricallyRegular_tensorProduct_of_algEquiv
    {R : Type u} {K L : Type v} (C : Type w) [CommRing R] [Field K] [Field L]
    [CommRing C] [Algebra R K] [Algebra R L] [Algebra R C]
    (e : K ≃ₐ[R] L) (h : Algebra.IsGeometricallyRegular K (K ⊗[R] C)) :
    Algebra.IsGeometricallyRegular L (L ⊗[R] C) := by
  constructor
  intro E _ _ _
  let : Algebra K L := e.toRingHom.toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  let : Algebra K E := ((algebraMap L E).comp e.toRingHom).toAlgebra
  have : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R E := ((algebraMap L E).comp (algebraMap R L)).toAlgebra
  have : IsScalarTower R L E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R K E := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap L E (algebraMap R L r) = algebraMap L E (e (algebraMap R K r))
    rw [e.commutes]
  have : Algebra.FiniteType K L := Algebra.FiniteType.of_surjective
    (Algebra.ofId K L) e.surjective
  have : Algebra.EssFiniteType K E := Algebra.EssFiniteType.comp K L E
  have := h.isRegularRing_tensorProduct E
  have : IsRegularRing (E ⊗[R] C) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange R K K E C).toRingEquiv
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange R L L E C).symm.toRingEquiv

private theorem isGeometricallyRegular_genericFormalFiber_of_isFractionRing
    (A : Type u) (K L : Type v) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [IsFractionRing A K] [IsFractionRing A L]
    (p : Ideal A) [p.IsPrime]
    (h :
      let T := AdicCompletion (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) ⊗[A] K
      letI : Algebra K T := Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyRegular K T) :
    let T := AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p) ⊗[A] L
    letI : Algebra L T := Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyRegular L T := by
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)
  let : Algebra K (C ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
  let : Algebra L (C ⊗[A] L) := Algebra.TensorProduct.rightAlgebra
  apply isGeometricallyRegular_of_algEquiv (Algebra.TensorProduct.commRight A L C)
  apply isGeometricallyRegular_tensorProduct_of_algEquiv C
    (IsLocalization.algEquiv (nonZeroDivisors A) K L)
  exact isGeometricallyRegular_of_algEquiv (Algebra.TensorProduct.commRight A K C).symm h

private theorem isGRing_of_genericFormalFibers_completeLocalDomains
    (h : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [IsDomain A] [IsPrecomplete (maximalIdeal A) A] (p : Ideal A) [p.IsPrime],
      let T := AdicCompletion (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) ⊗[A] (⊥ : Ideal A).ResidueField
      letI : Algebra (⊥ : Ideal A).ResidueField T := Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField T)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsPrecomplete (maximalIdeal R) R] : IsGRing R := by
  apply isGRing_iff_quotientCompletion_isGeometricallyRegular.mpr
  intro p q hqp
  let Q := R ⧸ q.asIdeal
  let : IsLocalRing Q := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsPrecomplete (maximalIdeal Q) Q :=
    isPrecomplete_maximalIdeal_of_surjective (R := R) Ideal.Quotient.mk_surjective
  let pQ : Ideal Q := p.asIdeal.map (Ideal.Quotient.mk q.asIdeal)
  have : pQ.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
  have hM : Submonoid.map (Ideal.Quotient.mk q.asIdeal) p.asIdeal.primeCompl =
      pQ.primeCompl := by
    simpa only [pQ, Ideal.comap_map_mk hqp] using
      Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk q.asIdeal)
        Ideal.Quotient.mk_surjective pQ
  dsimp only
  rw [hM, Localization.AtPrime.map_eq_maximalIdeal]
  exact isGeometricallyRegular_genericFormalFiber_of_isFractionRing Q
    (⊥ : Ideal Q).ResidueField q.asIdeal.ResidueField pQ (h Q pQ)

private theorem isGeometricallyRegular_genericFormalFiber_of_finite
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B))
    (h : ∀ (p : Ideal A) [p.IsPrime],
      let T := AdicCompletion (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) ⊗[A] (⊥ : Ideal A).ResidueField
      letI : Algebra (⊥ : Ideal A).ResidueField T := Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField T)
    (p : Ideal B) [p.IsPrime] :
    let T := AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p) ⊗[B] (⊥ : Ideal B).ResidueField
    letI : Algebra (⊥ : Ideal B).ResidueField T := Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyRegular (⊥ : Ideal B).ResidueField T := by
  have hf := (quasiFinite_preserves_geometricallyRegular_formalFibers_and_isGRing
    (R := A) (S := B) (⊥ : Ideal B) p bot_le).1
  have hbot : Ideal.under A (⊥ : Ideal B) = ⊥ := by
    ext x
    change algebraMap A B x = 0 ↔ x = 0
    exact ⟨fun hx => hinj (hx.trans (map_zero _).symm), fun hx => hx ▸ map_zero _⟩
  have hfraction : ∀ (q : Ideal A) [q.IsPrime], q = ⊥ → IsFractionRing A q.ResidueField := by
    rintro q _ rfl
    infer_instance
  have := hfraction _ hbot
  exact hf (isGeometricallyRegular_genericFormalFiber_of_isFractionRing A
    (⊥ : Ideal A).ResidueField (Ideal.under A (⊥ : Ideal B)).ResidueField
    (p.under A) (h (p.under A)))

/-- A Cohen ring that is a domain has characteristic zero. -/
public theorem charZero_of_isCohenRing (Λ : Type u) [CommRing Λ] [IsDomain Λ]
    [IsCohenRing Λ] : CharZero Λ := by
  obtain ⟨p, hp, hm⟩ := IsCohenRing.exists_prime_maximalIdeal_eq_span (R := Λ)
  have hzero : (p : Λ) ≠ 0 := fun hz =>
    IsDiscreteValuationRing.not_a_field Λ (by rw [hm, hz, Ideal.span_singleton_eq_bot])
  have hunit : ¬ IsUnit (p : Λ) := fun hu =>
    notMem_maximalIdeal.mpr hu (hm ▸ Ideal.mem_span_singleton_self _)
  apply (CharP.exists' Λ).resolve_right
  rintro ⟨q, ⟨hq⟩, _⟩
  rcases eq_or_ne p q with rfl | hne
  · exact hzero (CharP.cast_eq_zero Λ p)
  · exact hunit (isCoprime_zero_right.mp
      (CharP.cast_eq_zero Λ q ▸ ((Nat.coprime_primes hp hq).mpr hne).cast))

private theorem isGeometricallyRegular_genericFormalFiber_of_charZero
    (A : Type u) (K : Type v) [CommRing A] [IsRegularRing A] [CharZero A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (q : Ideal A) [q.IsPrime] :
    let T := AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q) ⊗[A] K
    letI : Algebra K T := Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyRegular K T := by
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing A
  exact isGeometricallyRegular_genericFormalFiber_of_perfectField A K q

private theorem isGRing_of_genericFormalFibers_mvPowerSeries
    (hpower : ∀ (k : Type u) [Field k] (n p : ℕ) [Fact p.Prime] [CharP k p]
      (q : Ideal (MvPowerSeries (Fin n) k)) [q.IsPrime],
      let A := MvPowerSeries (Fin n) k
      let T := AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q) ⊗[A] (⊥ : Ideal A).ResidueField
      letI : Algebra (⊥ : Ideal A).ResidueField T := Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField T)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsPrecomplete (maximalIdeal R) R] : IsGRing R := by
  apply isGRing_of_genericFormalFibers_completeLocalDomains ?_ R
  intro A _ _ _ _ _ p _
  have : IsAdicComplete (maximalIdeal A) A := ⟨⟩
  obtain ⟨n, Λ, hring, hdom, hcase, hreg, _, f, hinj, hfin, _⟩ :=
    IsLocalRing.exists_injective_finite_mvPowerSeries A
  let : CommRing Λ := hring
  have : IsDomain Λ := hdom
  have : IsRegularLocalRing (MvPowerSeries (Fin n) Λ) := hreg
  have : IsDomain (MvPowerSeries (Fin n) Λ) := IsRegularLocalRing.isDomain _
  let : Algebra (MvPowerSeries (Fin n) Λ) A := f.toAlgebra
  have : Module.Finite (MvPowerSeries (Fin n) Λ) A := hfin
  apply isGeometricallyRegular_genericFormalFiber_of_finite hinj ?_ p
  intro q _
  have : IsRegularRing (MvPowerSeries (Fin n) Λ) := isRegularRing_of_isRegularLocalRing _
  rcases hcase with hfield | hcohen
  · let : Field Λ := hfield.toField
    rcases CharP.exists' Λ with hzero | ⟨ell, hell, hchar⟩
    · have : CharZero (MvPowerSeries (Fin n) Λ) :=
        charZero_of_injective_ringHom MvPowerSeries.C_injective
      exact isGeometricallyRegular_genericFormalFiber_of_charZero _ _ q
    · exact hpower Λ n ell q
  · have : CharZero Λ := charZero_of_isCohenRing Λ
    have : CharZero (MvPowerSeries (Fin n) Λ) :=
      charZero_of_injective_ringHom MvPowerSeries.C_injective
    exact isGeometricallyRegular_genericFormalFiber_of_charZero _ _ q

/-- A Noetherian local ring complete for its maximal-ideal-adic topology is a G-ring. -/
@[stacks 07PS]
public theorem isGRing_of_isPrecomplete_maximalIdeal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsPrecomplete (maximalIdeal R) R] : IsGRing R := by
  apply isGRing_of_genericFormalFibers_mvPowerSeries ?_ R
  intro k _ n p _ _ q _
  have : IsDomain (MvPowerSeries (Fin n) k) := {}
  exact isGeometricallyRegular_formalFiber_mvPolynomial_mvPowerSeries (m := 0) (n := n) k
    (MvPowerSeries (Fin n) k) (⊥ : Ideal (MvPowerSeries (Fin n) k)).ResidueField
    ((MvPolynomial.isEmptyAlgEquiv (MvPowerSeries (Fin n) k) (Fin 0)).symm.restrictScalars k) q

end

end

end
