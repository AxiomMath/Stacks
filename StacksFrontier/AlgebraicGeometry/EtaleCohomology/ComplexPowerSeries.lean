module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.RingTheory.Etale.Field
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationCharacterization
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.Etale.StandardEtale
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.Unramified

/-!
# Étale algebras over the complex power-series ring

For the complex power-series ring `ℂ⟦t⟧`, an étale algebra is a finite product of copies of
the base and of punctured Kummer extensions `ℂ⟦t⟧[X, X⁻¹]/(Xⁿ - t)`. The latter are
supported over the punctured spectrum. Every étale cover of `Spec ℂ⟦t⟧` consequently has a
member admitting a section, so the identity cover refines it.

## Main definitions

* `Stacks.EtaleCohomology.puncturedKummerAlgebra` is the extension obtained by adjoining an
  `n`-th root of the parameter and inverting that root.

## Main results

* `Stacks.EtaleCohomology.exists_algEquiv_pi_puncturedKummerAlgebra` classifies étale
  algebras over `ℂ⟦t⟧`.
* `Stacks.EtaleCohomology.etale_puncturedKummerAlgebra` says the punctured Kummer factors
  are themselves étale.
* `Stacks.EtaleCohomology.isUnit_parameter_puncturedKummerAlgebra` says that the Kummer
  extensions factor through the punctured spectrum.
* `Stacks.EtaleCohomology.etaleCover_has_section` says that every étale cover of the
  spectrum has a member admitting a section.

## Implementation notes

The finite product has separate index types for the trivial and the Kummer factors. An
algebra equivalence over the power-series ring retains the structure maps, so the étaleness
of a Kummer factor is recorded separately from the classification. The factorization through
the punctured spectrum `D(t)` is expressed by invertibility of the image of the parameter.

## References

* [Stacks Project, Tag 03QI](https://stacks.math.columbia.edu/tag/03QI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial

universe u v

namespace Stacks.EtaleCohomology

/-- The ring of complex formal power series is a strictly henselian local ring: it is
complete, hence henselian, and its residue field `ℂ` is separably closed. -/
theorem powerSeries_strictlyHenselian :
    StrictlyHenselianLocalRing (PowerSeries ℂ) := by
  let R := PowerSeries ℂ
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete_maximalIdeal R
  have : IsSepClosed (IsLocalRing.ResidueField R) :=
    IsSepClosed.of_ringEquiv (PowerSeries.residueFieldOfPowerSeries (k := ℂ))
  exact ⟨⟩

/-- Over a henselian local ring, an étale algebra with a prime over the maximal ideal
inducing a bijection on residue fields gives a section of the corresponding morphism of
spectra. -/
private theorem spec_etale_section_of_residueField_bijective
    (R S : Type u) [CommRing R] [HenselianLocalRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] (P : Ideal S) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hbij : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
        (Algebra.ofId R S) (Ideal.LiesOver.over))) :
    ∃ s : Spec (.of R) ⟶ Spec (.of S),
      s ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = 𝟙 (Spec (.of R)) := by
  obtain ⟨ψ, _⟩ := henselian_etale_exists_section R S P hbij
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (algebraMap R S))) = _
  rw [show ψ.toRingHom.comp (algebraMap R S) = RingHom.id R from RingHom.ext ψ.commutes]
  exact Spec.map_id _

/-- Over a strictly henselian local ring, the residue-field map attached to any prime of
an étale algebra lying over the maximal ideal is bijective, because the residue field is
separably closed and the residue extension is separable. -/
private theorem residueFieldMap_bijective_of_strictlyHenselian
    (R S : Type*) [CommRing R] [StrictlyHenselianLocalRing R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) q
        (Algebra.ofId R S) (Ideal.LiesOver.over)) := by
  let p := IsLocalRing.maximalIdeal R
  let := Localization.AtPrime.algebraOfLiesOver p q
  let e : IsLocalRing.ResidueField R ≃+* p.ResidueField :=
    RingEquiv.ofBijective (algebraMap (R ⧸ p) p.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField p)
  have : IsSepClosed p.ResidueField := IsSepClosed.of_ringEquiv e.symm
  exact IsSepClosed.algebraMap_bijective p.ResidueField q.ResidueField

/-- A proper ideal of a domain with flat quotient is zero: flatness makes the quotient
torsion free, so the structure map is injective. -/
private theorem ideal_eq_bot_of_flat_quotient
    {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊤)
    [Module.Flat R (R ⧸ I)] : I = ⊥ := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : Module.IsTorsionFree R (R ⧸ I) := inferInstance
  have hinj := FaithfulSMul.algebraMap_injective R (R ⧸ I)
  apply le_antisymm _ bot_le
  intro x hx
  apply hinj
  simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hx)

/-- Over a strictly henselian local domain, an étale algebra splits as a finite product of
copies of the base times an étale algebra no prime of which lies over the maximal ideal. -/
private theorem exists_algEquiv_prod_of_etale_strictlyHenselian
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [StrictlyHenselianLocalRing R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    ∃ (n : ℕ) (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      Algebra.Etale R B ∧
      (∀ q : Ideal B, q.IsPrime → ¬ q.LiesOver (IsLocalRing.maximalIdeal R)) ∧
      Nonempty (A ≃ₐ[R] (Fin n → R) × B) := by
  classical
  obtain ⟨n, I, B, hB, hRB, ⟨e⟩, hI, hq⟩ :=
    Algebra.IsUnramifiedIn.exists_algEquiv_prod_quotient R A
      (fun q hq _ => inferInstance)
  let C := ∀ i, R ⧸ I i
  have : Algebra.Etale R (C × B) := Algebra.Etale.of_equiv e
  let : Algebra (C × B) B := (RingHom.snd C B).toAlgebra
  have : IsScalarTower R (C × B) B := .of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale R B := Algebra.Etale.comp R (C × B) B
  have : Module.Flat R C := Module.Flat.of_retract
    (LinearMap.inl R C B) (LinearMap.fst R C B) (by ext; rfl)
  have hI0 (i : Fin n) : I i = ⊥ := by
    have : Module.Flat R (R ⧸ I i) := Module.Flat.of_retract
      (LinearMap.single R (fun i => R ⧸ I i) i) (LinearMap.proj i)
      (by ext; simp)
    exact ideal_eq_bot_of_flat_quotient (I i) (hI i)
  let ei (i : Fin n) : (R ⧸ I i) ≃ₐ[R] R :=
    (Ideal.quotientEquivAlgOfEq R (hI0 i)).trans (AlgEquiv.quotientBot R R)
  exact ⟨n, B, hB, hRB, inferInstance, hq,
    ⟨e.trans ((AlgEquiv.piCongrRight ei).prodCongr (AlgEquiv.refl))⟩⟩

/-- If no prime of `B` lies over the maximal ideal of `R`, generated by `t`, then the image
of `t` in `B` is a unit. -/
private theorem isUnit_of_no_prime_liesOver
    (R B : Type*) [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hB : ∀ q : Ideal B, q.IsPrime → ¬ q.LiesOver (IsLocalRing.maximalIdeal R)) :
    IsUnit (algebraMap R B t) := by
  by_contra hu
  obtain ⟨q, hq, hle⟩ := (Ideal.span {algebraMap R B t}).exists_le_maximal
    (fun h => hu (Ideal.span_singleton_eq_top.mp h))
  apply hB q hq.isPrime
  constructor
  apply (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
    (Ideal.comap_ne_top (algebraMap R B) hq.ne_top)
  rw [ht, Ideal.span_le, Set.singleton_subset_iff]
  exact hle (Ideal.subset_span (Set.mem_singleton _))

/-- The fraction field of a discrete valuation ring is the localization away from any
uniformizer. -/
private theorem isLocalizationAway_of_irreducible
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht : Irreducible t) : IsLocalization.Away t K := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers t)
    (nonZeroDivisors R) ?_ ?_).mpr inferInstance
  · rintro y ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ ht.ne_zero)
  · intro y hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hy) ht
    refine ⟨t ^ n, ⟨n, rfl⟩, ⟨↑u⁻¹, ?_⟩⟩
    calc
      t ^ n = (↑u * ↑u⁻¹ : R) * t ^ n := by rw [Units.mul_inv, one_mul]
      _ = _ := by ring

/-- In a henselian local ring with separably closed residue field of characteristic zero,
every unit has an `n`-th root for every `n > 0`. -/
private theorem exists_pow_eq_unit_of_strictlyHenselian
    (R : Type*) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [CharZero (IsLocalRing.ResidueField R)]
    (n : ℕ) (hn : 0 < n) (u : Rˣ) : ∃ b : R, b ^ n = u := by
  let f : R[X] := X ^ n - C (u : R)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq
    (IsLocalRing.residue R u) hn
  have ha0 : a ≠ 0 := by
    intro h
    have hu := u.isUnit.map (IsLocalRing.residue R)
    rw [← ha, h, zero_pow hn.ne'] at hu
    exact not_isUnit_zero hu
  have lift := ((HenselianLocalRing.TFAE R).out 1 2).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨b, hb, _⟩ := lift f (monic_X_pow_sub_C _ hn.ne') a
    (by simpa [f] using sub_eq_zero.mpr ha)
    (by simp [f, Polynomial.derivative_X_pow, ha0, hn.ne'])
  exact ⟨b, by simpa [Polynomial.IsRoot, f, sub_eq_zero] using hb⟩

/-- The structure map from a domain to a field extension of its fraction field is
injective. -/
private theorem algebraMap_injective_of_isFractionRing
    (R K E : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E] :
    Function.Injective (algebraMap R E) := by
  rw [IsScalarTower.algebraMap_eq R K E]
  exact (algebraMap K E).injective.comp (IsFractionRing.injective R K)

/-- A finite separable extension of the fraction field of a strictly henselian discrete
valuation ring of residue characteristic zero is totally ramified: the uniformizer becomes a
`[L : K]`-th power. -/
private theorem exists_pow_finrank_eq_uniformizer
    (R K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [StrictlyHenselianLocalRing R] [CharZero (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L]
    (t : R) (ht : Irreducible t) :
    ∃ b : L, b ^ Module.finrank K L = algebraMap R L t := by
  classical
  let B := integralClosure R L
  obtain ⟨hfin, hnoeth, _, hded, n, m, hmmax, hm, hmlies, _, hdegree, hn, _⟩ :=
    IsDiscreteValuationRing.integralClosure_finite_dedekind_and_degree_eq_sum_ramification_inertia
      R K L
  have : Module.Finite R B := hfin
  have : IsNoetherianRing B := hnoeth
  have : IsDedekindDomain B := hded
  have hinj : Function.Injective (algebraMap R B) := by
    refine Function.Injective.of_comp (f := algebraMap B L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq R B L]
    exact algebraMap_injective_of_isFractionRing R K L
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hinj
  obtain ⟨hH, hlocal, hsep⟩ :=
    RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain
      (algebraMap R B) (Algebra.IsIntegral.isIntegral (R := R) (A := B))
  have : HenselianLocalRing B := hH
  have : IsLocalHom (algebraMap R B) := hlocal
  have : IsSepClosed (IsLocalRing.ResidueField B) := (hsep inferInstance).1
  have hnotfield : ¬ IsField B := fun h => IsDiscreteValuationRing.not_isField R
    (isField_of_isIntegral_of_isField hinj h)
  have : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnotfield).out 1 3).mpr hded
  have : IsDiscreteValuationRing.IsExtension R B := ⟨⟩
  have : CharZero (IsLocalRing.ResidueField B) :=
    charZero_of_injective_ringHom
      (IsLocalRing.ResidueField.map (algebraMap R B)).injective
  obtain rfl : n = 1 := hn inferInstance
  have hm0 : m 0 = IsLocalRing.maximalIdeal B := IsLocalRing.eq_maximalIdeal (hmmax 0)
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal R) := by
    rw [← hm0]
    exact hmlies 0
  have hf1 : (IsLocalRing.maximalIdeal B).inertiaDeg R = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal R)]
    apply Module.finrank_of_bijective_algebraMap
    change Function.Bijective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B))
    exact IsSepClosed.algebraMap_bijective _ _
  have he : IsDiscreteValuationRing.ramificationIndex R B = Module.finrank K L := by
    rw [Fin.sum_univ_one, hm0, hf1, mul_one] at hdegree
    rw [IsDiscreteValuationRing.ramificationIndex,
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx_def,
      Ideal.ramificationIdx'_eq_ramificationIdx _ _ (IsDiscreteValuationRing.not_a_field R)]
    exact hdegree.symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨hu, _, _, hpow⟩ := IsDiscreteValuationRing.ramificationIndex_characterization R B
  obtain ⟨u, hu⟩ := hpow t ht π hπ
  obtain ⟨a, ha⟩ := exists_pow_eq_unit_of_strictlyHenselian B
    (IsDiscreteValuationRing.ramificationIndex R B) (by omega) u
  refine ⟨algebraMap B L (a * π), ?_⟩
  rw [← he, ← map_pow, mul_pow, ha, ← hu, ← IsScalarTower.algebraMap_apply]

/-- The canonical map from `A[x]/(xⁿ - π)` to the Kummer field `K[x]/(xⁿ - π)` is
injective. -/
private theorem kummer_canonicalMap_injective
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht : Irreducible t) (n : ℕ) (hn : 0 < n) :
    Function.Injective (Stacks.KummerExtension.canonAlgHom K t n) := by
  have : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K t n)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K t n hn ht⟩
  have : FaithfulSMul R (Stacks.KummerExtension.K1 K t n) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap_injective_of_isFractionRing R K _)
  have hi : IsIntegral R (Stacks.KummerExtension.piRoot K t n) :=
    ⟨Stacks.KummerExtension.kummerPolyA t n, Stacks.KummerExtension.kummerPolyA_monic t n hn,
      Stacks.KummerExtension.kummerPolyA_eval_piRoot K t n⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [AdjoinRoot.mk_eq_zero, ← Stacks.KummerExtension.minpoly_piRoot K t n hn ht]
  apply minpoly.isIntegrallyClosed_dvd hi
  simpa [Stacks.KummerExtension.canonAlgHom, AdjoinRoot.liftAlgHom_mk,
    Polynomial.aeval_def] using hz

/-- The Kummer field `K[π^{1/n}]` is the localization of `A[x]/(xⁿ - π)` away from the
adjoined root. -/
private theorem kummerField_equiv_localization
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht : Irreducible t) (n : ℕ) (hn : 0 < n) :
    Nonempty (Stacks.KummerExtension.K1 K t n ≃ₐ[R]
      Localization.Away (AdjoinRoot.root ((X : R[X]) ^ n - C t))) := by
  let E := Stacks.KummerExtension.K1 K t n
  let D := Stacks.KummerExtension.A' t n
  let θ : E := Stacks.KummerExtension.piRoot K t n
  let r : D := Stacks.KummerExtension.piRootA t n
  let φ : D →ₐ[R] E := Stacks.KummerExtension.canonAlgHom K t n
  let : Algebra D E := φ.toRingHom.toAlgebra
  have : IsScalarTower R D E := .of_algebraMap_eq fun x => (φ.commutes x).symm
  have : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K t n)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K t n hn ht⟩
  have hθ : θ ^ n = algebraMap R E t := Stacks.KummerExtension.piRoot_pow K t n
  have hθ0 : θ ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hθ
    refine ht.ne_zero (algebraMap_injective_of_isFractionRing R K E ?_)
    rw [map_zero]
    exact hθ.symm
  have hr : algebraMap D E r = θ := Stacks.KummerExtension.canonAlgHom_piRootA K t n
  have : IsLocalization.Away r E := by
    refine IsLocalization.Away.mk r (by rwa [hr, isUnit_iff_ne_zero]) ?_ ?_
    · intro z
      obtain ⟨m, hm⟩ := Stacks.KummerExtension.exists_pow_smul_mem_adjoin_piRoot K t n hn ht z
      rw [← Stacks.KummerExtension.canonAlgHom_range_eq_adjoin K t n hn] at hm
      obtain ⟨d, hd⟩ := hm
      refine ⟨n * m, d, ?_⟩
      rw [hr, pow_mul, hθ]
      change z * (algebraMap R E t) ^ m = φ d
      simpa [φ, Algebra.smul_def, map_pow, mul_comm] using hd.symm
    · intro a b hab
      exact ⟨0, by simp [kummer_canonicalMap_injective R K t ht n hn hab]⟩
  exact ⟨(IsLocalization.algEquiv (Submonoid.powers r) E (Localization.Away r)).restrictScalars R⟩

/-- Over a strictly henselian discrete valuation ring of residue characteristic zero, a
finite separable extension of the fraction field is a punctured Kummer extension of degree
`[L : K]`. -/
private theorem finiteExtension_equiv_puncturedKummer
    (R K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [StrictlyHenselianLocalRing R] [CharZero (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L]
    (t : R) (ht : Irreducible t) :
    Nonempty (L ≃ₐ[R] Localization.Away
      (AdjoinRoot.root ((X : R[X]) ^ Module.finrank K L - C t))) := by
  let n := Module.finrank K L
  have hn : 0 < n := Module.finrank_pos
  have hirr := Stacks.KummerExtension.kummerPoly_irreducible K t n hn ht
  have : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K t n)) := ⟨hirr⟩
  obtain ⟨b, hb⟩ := exists_pow_finrank_eq_uniformizer R K L t ht
  let φ : Stacks.KummerExtension.K1 K t n →ₐ[K] L :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId K L) b (by
      simpa [Stacks.KummerExtension.kummerPoly, sub_eq_zero,
        ← IsScalarTower.algebraMap_apply R K L] using hb)
  have hrank : Module.finrank K (Stacks.KummerExtension.K1 K t n) = Module.finrank K L := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
      Stacks.KummerExtension.kummerPoly_natDegree]
  let e := AlgEquiv.ofBijective φ ⟨φ.injective,
    (LinearEquiv.ofInjectiveOfFinrankEq φ.toLinearMap φ.injective hrank).surjective⟩
  obtain ⟨e'⟩ := kummerField_equiv_localization R K t ht n hn
  exact ⟨(e.restrictScalars R).symm.trans e'⟩

/-- The punctured extension of `ℂ⟦t⟧` obtained by adjoining an `n`-th root of `t`.
The localization is the presentation `ℂ⟦t⟧[X,X⁻¹]/(Xⁿ-t)`. -/
abbrev puncturedKummerAlgebra (n : ℕ) :=
  Localization.Away
    (AdjoinRoot.root
      ((Polynomial.X : (PowerSeries ℂ)[X]) ^ n - Polynomial.C PowerSeries.X))

/-- Every étale algebra over `ℂ⟦t⟧` is a finite product of trivial factors and
punctured Kummer extensions of positive degree. -/
@[stacks 03QI "classification of étale algebras"]
theorem exists_algEquiv_pi_puncturedKummerAlgebra
    (A : Type*) [CommRing A] [Algebra (PowerSeries ℂ) A]
    [Algebra.Etale (PowerSeries ℂ) A] :
    ∃ (ι κ : Type*) (_ : Finite ι) (_ : Finite κ) (n : κ → ℕ),
      (∀ j, 0 < n j) ∧
      Nonempty (A ≃ₐ[PowerSeries ℂ]
        (ι → PowerSeries ℂ) × (∀ j, puncturedKummerAlgebra (n j))) := by
  classical
  let R := PowerSeries ℂ
  let K := FractionRing R
  have : StrictlyHenselianLocalRing R := powerSeries_strictlyHenselian
  have : CharZero (IsLocalRing.ResidueField R) :=
    (PowerSeries.residueFieldOfPowerSeries (k := ℂ)).toRingHom.charZero
  have hX : Irreducible (PowerSeries.X : R) := PowerSeries.X_irreducible
  have : IsLocalization.Away (PowerSeries.X : R) K :=
    isLocalizationAway_of_irreducible R K PowerSeries.X hX
  have : Algebra.Etale R K := Algebra.Etale.of_isLocalizationAway PowerSeries.X
  obtain ⟨m, B, hB, hRB, hEtB, hq, ⟨eA⟩⟩ :=
    exists_algEquiv_prod_of_etale_strictlyHenselian R A
  have hunit : IsUnit (algebraMap R B PowerSeries.X) :=
    isUnit_of_no_prime_liesOver R B PowerSeries.X PowerSeries.maximalIdeal_eq_span_X hq
  let : Algebra K B := (IsLocalization.Away.lift (S := K) PowerSeries.X hunit).toAlgebra
  have : IsScalarTower R K B := .of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq PowerSeries.X hunit x).symm
  have : Algebra.Etale K B := Algebra.Etale.of_restrictScalars R K B
  obtain ⟨J, hJ, E, hE, hKE, eB, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  let : Fintype J := Fintype.ofFinite J
  let (j : J) : Algebra R (E j) :=
    ((algebraMap K (E j)).comp (algebraMap R K)).toAlgebra
  have (j : J) : IsScalarTower R K (E j) := .of_algebraMap_eq fun _ => rfl
  have (j : J) : Module.Finite K (E j) := (hfin j).1
  have (j : J) : Algebra.IsSeparable K (E j) := (hfin j).2
  let d (j : J) := Module.finrank K (E j)
  let eK (j : J) : E j ≃ₐ[R] puncturedKummerAlgebra (d j) :=
    (finiteExtension_equiv_puncturedKummer R K (E j) PowerSeries.X hX).some
  let e : A ≃ₐ[R] (Fin m → R) × (∀ j, puncturedKummerAlgebra (d j)) :=
    eA.trans ((AlgEquiv.refl).prodCongr
      ((eB.restrictScalars R).trans (AlgEquiv.piCongrRight eK)))
  exact ⟨ULift (Fin m), ULift (Fin (Fintype.card J)), inferInstance, inferInstance,
    fun j => d ((Fintype.equivFin J).symm j.down), fun _ => Module.finrank_pos,
    ⟨e.trans ((AlgEquiv.piCongrLeft' R _ Equiv.ulift.symm).prodCongr
      (AlgEquiv.piCongrLeft' R _ ((Fintype.equivFin J).trans Equiv.ulift.symm)))⟩⟩

/-- A punctured Kummer extension of positive degree is étale over `ℂ⟦t⟧`. -/
@[stacks 03QI "étaleness of the Kummer extensions"]
theorem etale_puncturedKummerAlgebra (n : ℕ) (hn : 0 < n) :
    Algebra.Etale (PowerSeries ℂ) (puncturedKummerAlgebra n) := by
  let f : (PowerSeries ℂ)[X] := X ^ n - C PowerSeries.X
  let P : StandardEtalePair (PowerSeries ℂ) :=
    { f := f
      monic_f := monic_X_pow_sub_C _ hn.ne'
      g := X
      cond := by
        let c : PowerSeries ℂ := algebraMap ℂ (PowerSeries ℂ) ((n : ℂ)⁻¹)
        let p₁ : (PowerSeries ℂ)[X] := Polynomial.C c * X
        refine ⟨p₁, 0, n, ?_⟩
        dsimp [f]
        rw [mul_zero, add_zero, Polynomial.derivative_sub,
          Polynomial.derivative_X_pow, Polynomial.derivative_C]
        have hnc : (n : PowerSeries ℂ) * c = 1 := by
          change PowerSeries.C (n : ℂ) * PowerSeries.C ((n : ℂ)⁻¹) = 1
          rw [← map_mul]
          simp [hn.ne']
        calc
          _ = (Polynomial.C (n : PowerSeries ℂ) * Polynomial.C c) *
              (X ^ (n - 1) * X) := by
                dsimp [p₁]
                ring
          _ = X ^ n := by
            rw [← C_mul, hnc, ← pow_succ, Nat.sub_add_cancel hn]
            simp }
  exact Algebra.Etale.of_equiv
    (P.equivAwayAdjoinRoot : P.Ring ≃ₐ[PowerSeries ℂ] puncturedKummerAlgebra n)

/-- The parameter is invertible on a punctured Kummer extension, so its spectrum
maps into `D(t)`. -/
@[stacks 03QI "factorization through the punctured spectrum"]
theorem isUnit_parameter_puncturedKummerAlgebra (n : ℕ) :
    IsUnit (algebraMap (PowerSeries ℂ) (puncturedKummerAlgebra n) PowerSeries.X) := by
  let f : (PowerSeries ℂ)[X] := X ^ n - C PowerSeries.X
  have hroot : (AdjoinRoot.root f) ^ n =
      algebraMap (PowerSeries ℂ) (AdjoinRoot f) PowerSeries.X := by
    have h := AdjoinRoot.eval₂_root f
    change eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f)
      (X ^ n - C PowerSeries.X) = 0 at h
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
    exact sub_eq_zero.mp h
  change IsUnit (algebraMap (PowerSeries ℂ)
    (Localization.Away (AdjoinRoot.root f)) PowerSeries.X)
  rw [IsScalarTower.algebraMap_apply (PowerSeries ℂ) (AdjoinRoot f)
    (Localization.Away (AdjoinRoot.root f)) PowerSeries.X, ← hroot, map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit _).pow n

/-- An étale covering of `Spec ℂ⟦t⟧` has a member whose structure morphism
admits a section, so the identity cover refines it. -/
@[stacks 03QI "refinement by the identity cover"]
theorem etaleCover_has_section
    (𝒰 : (Spec (.of (PowerSeries ℂ))).Cover Scheme.etalePrecoverage) :
    ∃ i : 𝒰.I₀, ∃ s : Spec (.of (PowerSeries ℂ)) ⟶ 𝒰.X i,
      s ≫ 𝒰.f i = 𝟙 (Spec (.of (PowerSeries ℂ))) := by
  let R := PowerSeries ℂ
  have : StrictlyHenselianLocalRing R := powerSeries_strictlyHenselian
  let x : Spec (.of R) := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  change (Spec (.of R)).Cover (Scheme.precoverage @Etale) at 𝒰
  obtain ⟨i, y, hy⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).mp 𝒰.mem₀).1 x
  obtain ⟨S, g, hg, z, hz⟩ := Scheme.exists_Spec_apply_eq y
  let f : CommRingCat.of R ⟶ S := Spec.preimage (g ≫ 𝒰.f i)
  have hf : Spec.map f = g ≫ 𝒰.f i := Spec.map_preimage _
  let : Algebra R S := f.hom.toAlgebra
  have hEt : Etale (Spec.map f) := by
    rw [hf]
    infer_instance
  have : Algebra.Etale R S :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hEt
  have hpoint : PrimeSpectrum.comap (algebraMap R S) z = x := by
    change (Spec.map f) z = x
    rw [hf, Scheme.Hom.comp_apply, hz, hy]
  have : z.asIdeal.IsPrime := z.isPrime
  have : z.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(congrArg PrimeSpectrum.asIdeal hpoint).symm⟩
  obtain ⟨s, hs⟩ := spec_etale_section_of_residueField_bijective R S z.asIdeal
    (residueFieldMap_bijective_of_strictlyHenselian R S z.asIdeal)
  refine ⟨i, s ≫ g, ?_⟩
  rw [Category.assoc, ← hf]
  exact hs

end Stacks.EtaleCohomology
