module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution.ReducedTensorLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 09II from Epp's theorem: Dedekind integral closures and local solutions

Part 4 of the development of Stacks Tag 09II from Epp's theorem (Tag 09F9) in
`StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution`. It contains
Dedekind and discrete valuation ring properties of integral closures and their localizations at
primes, residue field and faithfulness facts along integral towers, and the merge of the finitely
many local solutions into one finite extension via Tag 0GLR
(`exists_finite_extension_localSolutions_of_perfectField`).
-/

@[expose] public section

universe uA uB uK uL v uK₁ uL₁ uA₁ uB₁

namespace Stacks.EliminateRamification

open IsLocalRing
open scoped TensorProduct

/-- Compatibility over a ring determines compatibility over its localization. -/
private theorem isScalarTower_of_isLocalization_base
    (R K S T : Type*) [CommSemiring R] [CommSemiring K] [CommSemiring S] [CommSemiring T]
    [Algebra R K] [Algebra R S] [Algebra K S] [IsScalarTower R K S]
    [Algebra R T] [Algebra K T] [IsScalarTower R K T]
    [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid R) [IsLocalization M K] : IsScalarTower K S T :=
  IsScalarTower.of_algebraMap_eq fun k =>
    ((IsScalarTower.toAlgHom R S T).extendScalarsOfIsLocalization K M).commutes k |>.symm

/-- In a DVR, any regular multiplicative set containing a nonunit gives the fraction ring. -/
private theorem isLocalization_of_isFractionRing_of_isDiscreteValuationRing
    (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing F] [Algebra R F] [IsFractionRing R F]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    (hunit : ∃ x ∈ M, ¬ IsUnit x) : IsLocalization M F := by
  obtain ⟨b, hb, hbunit⟩ := hunit
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπb : π ∣ b := by
    have hbmem : b ∈ maximalIdeal R := (mem_maximalIdeal b).mpr hbunit
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hbmem
  apply (IsLocalization.iff_of_le_of_exists_dvd M (nonZeroDivisors R) hM ?_).mpr
    (inferInstance : IsFractionRing R F)
  intro x hx
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero hx) hπ
  exact ⟨b ^ n, M.pow_mem hb n, hn.dvd_iff_dvd_left.mpr (pow_dvd_pow_of_dvd hπb n)⟩

/-- The fraction field of a normalized local DVR is the corresponding localization of the generic
algebra. -/
theorem exists_isLocalization_fractionRing_atPrime_integralClosure
    (R K T : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [CommRing T] [Algebra K T] [Algebra R T] [IsScalarTower R K T]
    [Algebra.IsIntegral K T]
    (q : Ideal (integralClosure R T)) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    [FaithfulSMul R (Localization.AtPrime q)]
    [IsLocalHom (algebraMap R (Localization.AtPrime q))] :
    letI : Algebra (Localization.AtPrime q) (FractionRing (Localization.AtPrime q)) :=
      OreLocalization.instAlgebra (R₀ := Localization.AtPrime q)
        (R := Localization.AtPrime q) (S := nonZeroDivisors (Localization.AtPrime q))
    ∃ (_ : Algebra T (FractionRing (Localization.AtPrime q))),
      (∀ x : integralClosure R T, algebraMap T (FractionRing (Localization.AtPrime q)) x.val =
        algebraMap (Localization.AtPrime q) (FractionRing (Localization.AtPrime q))
          (algebraMap (integralClosure R T) (Localization.AtPrime q) x)) ∧
      IsLocalization (Algebra.algebraMapSubmonoid T q.primeCompl)
        (FractionRing (Localization.AtPrime q)) := by
  let C := integralClosure R T
  let Cq := Localization.AtPrime q
  let F := FractionRing Cq
  let : CommRing Cq := inferInstanceAs (CommRing (Localization.AtPrime q))
  let : CommRing F := inferInstanceAs (CommRing (FractionRing Cq))
  let algCqF : Algebra Cq F :=
    OreLocalization.instAlgebra (R₀ := Localization.AtPrime q)
      (R := Localization.AtPrime q) (S := nonZeroDivisors (Localization.AtPrime q))
  let : SMul Cq F := algCqF.toSMul
  let : Module Cq F := algCqF.toModule
  have : IsFractionRing Cq F := inferInstanceAs (IsFractionRing Cq (FractionRing Cq))
  let algCCq : Algebra C Cq := inferInstanceAs (Algebra C (Localization.AtPrime q))
  let : SMul C Cq := algCCq.toSMul
  let algCF : Algebra C F :=
    OreLocalization.instAlgebra (R₀ := C) (R := Localization.AtPrime q)
      (S := nonZeroDivisors (Localization.AtPrime q))
  let : SMul C F := algCF.toSMul
  let : Module C F := algCF.toModule
  have : IsScalarTower C Cq F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let M := Algebra.algebraMapSubmonoid C (nonZeroDivisors R)
  have : IsLocalization M T :=
    Stacks.DiscreteValuationRing.Ramification.isLocalization_integralClosure_of_isIntegral
      R K T (integralClosure R T) (nonZeroDivisors R)
  have hM : Algebra.algebraMapSubmonoid Cq M ≤ nonZeroDivisors Cq := by
    rintro _ ⟨x, ⟨r, hr, rfl⟩, rfl⟩
    rw [← IsScalarTower.algebraMap_apply R C Cq]
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff (algebraMap R Cq) (FaithfulSMul.algebraMap_injective R Cq)).mpr
        (nonZeroDivisors.ne_zero hr))
  have hunit : ∃ x ∈ Algebra.algebraMapSubmonoid Cq M, ¬ IsUnit x := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    refine ⟨algebraMap R Cq π, ?_, ?_⟩
    · refine ⟨algebraMap R C π, ⟨π, mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero, rfl⟩, ?_⟩
      exact (IsScalarTower.algebraMap_apply R C Cq π).symm
    · intro h
      exact hπ.not_isUnit (isUnit_of_map_unit (algebraMap R Cq) π h)
  have : IsLocalization (Algebra.algebraMapSubmonoid Cq M) F :=
    isLocalization_of_isFractionRing_of_isDiscreteValuationRing Cq F _ hM hunit
  have hmap (y : M) : IsUnit (algebraMap C F y) := by
    rw [IsScalarTower.algebraMap_apply C Cq F]
    exact IsLocalization.map_units (M := Algebra.algebraMapSubmonoid Cq M) F
      ⟨algebraMap C Cq y, ⟨y, y.property, rfl⟩⟩
  let f : T →ₐ[C] F := IsLocalization.liftAlgHom (f := Algebra.ofId C F) hmap
  let := f.toAlgebra
  let : SMul C T := C.toAlgebra.toSMul
  let : SMul C F := (inferInstance : Algebra C F).toSMul
  have : IsScalarTower C T F := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  exact ⟨inferInstance, fun x => f.commutes x, IsLocalization.commutes T Cq F M q.primeCompl⟩

/-- The integral closure of `Base` in a field which is the fraction field of the image of a
Noetherian integral `Base`-algebra of dimension at most one is a Dedekind domain. -/
private theorem integralClosure_isDedekind_of_fractionRing_range
    (Base : Type*) (Intermediate : Type*)
    (Ambient : Type*)
    [CommRing Base] [CommRing Intermediate] [Field Ambient]
    [Algebra Base Intermediate] [Algebra Intermediate Ambient] [Algebra Base Ambient]
    [IsScalarTower Base Intermediate Ambient] [Algebra.IsIntegral Base Intermediate]
    [IsNoetherianRing Intermediate] [Ring.KrullDimLE 1 Intermediate]
    [IsFractionRing (IsScalarTower.toAlgHom Base Intermediate Ambient).range Ambient] :
    IsDedekindDomain (integralClosure Base Ambient) := by
  let comparison := IsScalarTower.toAlgHom Base Intermediate Ambient
  let image := comparison.range
  have : IsNoetherianRing image :=
    isNoetherianRing_of_surjective Intermediate image comparison.rangeRestrict.toRingHom
      comparison.rangeRestrict_surjective
  have : Ring.KrullDimLE 1 image := Ring.krullDimLE_iff.mpr <|
    (ringKrullDim_le_of_surjective comparison.rangeRestrict.toRingHom
      comparison.rangeRestrict_surjective).trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 Intermediate))
  have : Ring.DimensionLEOne image :=
    ⟨fun nonzero prime => prime.isMaximal_of_ne_bot nonzero⟩
  have : Algebra.IsIntegral Base image :=
    Algebra.IsIntegral.of_surjective comparison.rangeRestrict comparison.rangeRestrict_surjective
  have dedekind := IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
    image Ambient Ambient (integralClosure image Ambient)
  have : IsDedekindDomain (integralClosure image Ambient) := dedekind.1
  have closuresEqual : (integralClosure Base Ambient).toSubring =
      (integralClosure image Ambient).toSubring := by
    ext element
    exact ⟨fun integral => integral.tower_top,
      fun integral => isIntegral_trans (R := Base) element integral⟩
  show IsDedekindDomain ↥(integralClosure Base Ambient).toSubring
  rw [closuresEqual]
  infer_instance

/-- An element of a finite product is integral iff each component is integral. -/
private theorem integral_pi_iff_of_finite
    (Base : Type*) [CommRing Base]
    (Index : Type*) [Finite Index]
    (Factor : Index → Type*) [∀ index, CommRing (Factor index)]
    [∀ index, Algebra Base (Factor index)] (element : ∀ index, Factor index) :
    IsIntegral Base element ↔ ∀ index, IsIntegral Base (element index) := by
  classical
  let := Fintype.ofFinite Index
  constructor
  · intro integral index
    obtain ⟨polynomial, monic, vanishing⟩ := integral
    refine ⟨polynomial, monic, ?_⟩
    have equality := congrFun vanishing index
    change (polynomial.aeval element) index = 0 at equality
    show polynomial.aeval (element index) = 0
    simpa only [Polynomial.aeval_pi_apply₂] using equality
  · intro integral
    choose polynomial monic vanishing using integral
    refine ⟨∏ index, polynomial index,
      Polynomial.monic_prod_of_monic _ _ (fun index _ => monic index), ?_⟩
    apply funext
    intro index
    show ((∏ component, polynomial component).aeval element) index = 0
    rw [Polynomial.aeval_pi_apply₂]
    simp only [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ index) (vanishing index)

/-- Integral closure in a finite product is the product of the integral closures. -/
private noncomputable def integralClosure_productEquiv
    (Base : Type*) [CommRing Base]
    (Index : Type*) [Finite Index]
    (Factor : Index → Type*) [∀ index, CommRing (Factor index)]
    [∀ index, Algebra Base (Factor index)] :
    integralClosure Base (∀ index, Factor index) ≃+*
      (∀ index, integralClosure Base (Factor index)) where
  toFun element := fun index =>
    ⟨element.val index,
      (integral_pi_iff_of_finite Base Index Factor element.val).mp element.property index⟩
  invFun element := ⟨fun index => (element index).val,
    (integral_pi_iff_of_finite Base Index Factor _).mpr (fun index => (element index).property)⟩
  left_inv _ := Subtype.ext (funext fun _ => rfl)
  right_inv _ := funext fun _ => Subtype.ext rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The integral closure in a reduced Artinian ring is the product of the integral closures of its
residue fields. -/
private noncomputable def integralClosure_equivPi
    (R T : Type*) [CommRing R] [CommRing T] [Algebra R T] [IsArtinianRing T] [IsReduced T] :
    integralClosure R T ≃ₐ[R] (∀ m : MaximalSpectrum T, integralClosure R (T ⧸ m.asIdeal)) :=
  ((IsArtinianRing.equivPi T).restrictScalars R).mapIntegralClosure.trans
    { __ := integralClosure_productEquiv R (MaximalSpectrum T) fun m => T ⧸ m.asIdeal
      commutes' _ := rfl }

/-- The integral closure in a reduced Artinian ring, under the fraction-field condition on every
factor, is a finite product of Dedekind domains. -/
private theorem integralClosure_finiteProduct_dedekind
    (Base : Type*) (Intermediate : Type*)
    (Ambient : Type*)
    [CommRing Base] [CommRing Intermediate] [CommRing Ambient]
    [Algebra Base Intermediate] [Algebra Intermediate Ambient] [Algebra Base Ambient]
    [IsScalarTower Base Intermediate Ambient] [Algebra.IsIntegral Base Intermediate]
    [IsNoetherianRing Intermediate] [Ring.KrullDimLE 1 Intermediate]
    [IsArtinianRing Ambient] [IsReduced Ambient]
    (fractionFields : ∀ maximal : MaximalSpectrum Ambient,
      IsFractionRing (IsScalarTower.toAlgHom Base Intermediate
        (Ambient ⧸ maximal.asIdeal)).range (Ambient ⧸ maximal.asIdeal)) :
    Finite (MaximalSpectrum Ambient) ∧
      (∀ maximal : MaximalSpectrum Ambient,
        IsDedekindDomain (integralClosure Base (Ambient ⧸ maximal.asIdeal))) ∧
      Nonempty (integralClosure Base Ambient ≃ₐ[Base]
        (∀ maximal : MaximalSpectrum Ambient,
          integralClosure Base (Ambient ⧸ maximal.asIdeal))) := by
  let Factor (maximal : MaximalSpectrum Ambient) := Ambient ⧸ maximal.asIdeal
  let (maximal : MaximalSpectrum Ambient) : Field (Factor maximal) :=
    Ideal.Quotient.field maximal.asIdeal
  refine ⟨inferInstance, ?_, ?_⟩
  · intro maximal
    have := fractionFields maximal
    exact integralClosure_isDedekind_of_fractionRing_range Base Intermediate (Factor maximal)
  · exact ⟨integralClosure_equivPi Base Ambient⟩

/-- A directed union equal to a finitely generated algebra contains that algebra at a finite
stage. -/
private theorem exists_subalgebra_eq_top_of_directed_cover
    (R S : Type*) [CommSemiring R] [Semiring S]
    [Algebra R S] [Algebra.FiniteType R S]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (T : ι → Subalgebra R S) (hT : Monotone T)
    (hcover : ∀ x : S, ∃ i, x ∈ T i) :
    ∃ i, ∀ j, i ≤ j → T j = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := R) (A := S))
  choose f hf using fun x : s => hcover x.val
  obtain ⟨i, hi⟩ := Finite.exists_le f
  refine ⟨i, fun j hij => top_unique ?_⟩
  rw [← hs, Algebra.adjoin_le_iff]
  intro x hx
  exact hT ((hi ⟨x, hx⟩).trans hij) (hf ⟨x, hx⟩)

/-- A Noetherian integral closure of a one-dimensional ring in a field is a Dedekind domain. -/
private theorem isDedekindDomain_integralClosure_of_isNoetherianRing
    (R F : Type*) [CommRing R] [Nontrivial R] [Ring.DimensionLEOne R]
    [Field F] [Algebra R F] [IsNoetherianRing (integralClosure R F)] :
    IsDedekindDomain (integralClosure R F) := by
  have : Ring.DimensionLEOne (integralClosure R F) :=
    Ring.DimensionLEOne.of_isIntegral R _
  have : IsIntegrallyClosed (integralClosure R F) :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure R F) F
  exact { toIsDomain := inferInstance
          toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance }

/-- A maximal ideal in an injective integral extension of a discrete valuation ring is nonzero. -/
private theorem ne_bot_of_isMaximal_of_isIntegral_dvr
    (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (q : Ideal S) [q.IsMaximal] : q ≠ ⊥ := by
  have hc : q.comap (algebraMap R S) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q)
  intro hq
  apply IsDiscreteValuationRing.not_a_field R
  rw [← hc, hq]
  show RingHom.ker (algebraMap R S) = ⊥
  exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)

/-- Every maximal localization of a Noetherian integral closure of a discrete valuation ring is a
DVR. -/
private theorem isDiscreteValuationRing_integralClosure_atPrime
    (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [FaithfulSMul R F]
    [IsNoetherianRing (integralClosure R F)]
    (q : Ideal (integralClosure R F)) [q.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have : IsDedekindDomain (integralClosure R F) :=
    isDedekindDomain_integralClosure_of_isNoetherianRing R F
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _
      (ne_bot_of_isMaximal_of_isIntegral_dvr R _ q) _

/-- Noetherianness of the normalization passes to every field factor of a reduced Artinian ring. -/
private theorem isNoetherianRing_integralClosure_quotient
    (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]
    [IsArtinianRing T] [IsReduced T] [IsNoetherianRing (integralClosure R T)]
    (m : MaximalSpectrum T) :
    IsNoetherianRing (integralClosure R (T ⧸ m.asIdeal)) := by
  let e' := (integralClosure_equivPi R T).toRingEquiv
  exact isNoetherianRing_of_surjective (integralClosure R T) _
    ((Pi.evalRingHom (fun q : MaximalSpectrum T => integralClosure R (T ⧸ q.asIdeal)) m).comp
      e'.toRingHom) ((Function.surjective_eval m).comp e'.surjective)

/-- Every maximal localization of the normalization in a reduced Artinian algebra is a DVR. -/
theorem isDiscreteValuationRing_integralClosure_localization
    (R K T : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [FaithfulSMul R K]
    [CommRing T] [Algebra K T] [Algebra R T] [IsScalarTower R K T]
    [IsArtinianRing T] [IsReduced T] [IsNoetherianRing (integralClosure R T)]
    (q : Ideal (integralClosure R T)) [q.IsMaximal] :
    ∃ (_ : IsDomain (Localization.AtPrime q)),
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  classical
  let F (m : MaximalSpectrum T) := T ⧸ m.asIdeal
  let C (m : MaximalSpectrum T) : Type _ := integralClosure R (F m)
  let (m : MaximalSpectrum T) : Field (F m) := Ideal.Quotient.field _
  have (m : MaximalSpectrum T) : IsNoetherianRing (C m) :=
    isNoetherianRing_integralClosure_quotient R T m
  have (m : MaximalSpectrum T) : IsDedekindDomain (C m) :=
    isDedekindDomain_integralClosure_of_isNoetherianRing R (F m)
  let e : integralClosure R T ≃+* (∀ m, C m) := (integralClosure_equivPi R T).toRingEquiv
  let q' := q.comap e.symm.toRingHom
  have : q'.IsMaximal := Ideal.comap_isMaximal_of_surjective e.symm.toRingHom e.symm.surjective
  obtain ⟨m, r, hr⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq (⟨q', inferInstance⟩)
  have heq : r.asIdeal.comap (Pi.evalRingHom C m) = q' :=
    congrArg PrimeSpectrum.asIdeal hr
  have hmap : q'.map (Pi.evalRingHom C m) = r.asIdeal := by
    rw [← heq]
    exact Ideal.map_comap_of_surjective _ (Function.surjective_eval m) _
  have : r.asIdeal.IsMaximal := by
    have h := Ideal.map_eq_top_or_isMaximal_of_surjective (Pi.evalRingHom C m)
      (Function.surjective_eval m) (inferInstance : q'.IsMaximal)
    rw [hmap] at h
    exact h.resolve_left r.isPrime.ne_top
  have : FaithfulSMul R (F m) :=
    (faithfulSMul_iff_algebraMap_injective R (F m)).mpr (by
      rw [IsScalarTower.algebraMap_eq R K (F m)]
      exact (algebraMap K (F m)).injective.comp (FaithfulSMul.algebraMap_injective R K))
  have : IsDiscreteValuationRing (Localization.AtPrime r.asIdeal) :=
    isDiscreteValuationRing_integralClosure_atPrime R (F m) r.asIdeal
  let e₁ := Localization.localRingEquiv q (r.asIdeal.comap (Pi.evalRingHom C m)) e (by
    rw [heq]
    ext x
    show x ∈ q ↔ e.symm (e x) ∈ q
    rw [e.symm_apply_apply])
  let e₂ := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom r.asIdeal)
    (Localization.AtPrime.mapPiEvalRingHom_bijective r.asIdeal)
  let eLoc := e₁.trans e₂
  have : IsDomain (Localization.AtPrime q) := eLoc.injective.isDomain eLoc.toRingHom
  exact ⟨inferInstance, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eLoc.symm⟩

/-- A maximal ideal contracts to the maximal ideal of an intermediate DVR in a local integral
square. -/
theorem comap_eq_maximalIdeal_of_integral_tower
    (A B R C : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [FaithfulSMul A R]
    [CommRing C] [Algebra B C] [Algebra.IsIntegral B C]
    [Algebra A C] [IsScalarTower A B C] [Algebra R C] [IsScalarTower A R C]
    (q : Ideal C) [q.IsMaximal] :
    q.comap (algebraMap R C) = maximalIdeal R := by
  have hB : q.comap (algebraMap B C) = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q)
  have hA : q.comap (algebraMap A C) = maximalIdeal A := by
    rw [IsScalarTower.algebraMap_eq A B C, ← Ideal.comap_comap, hB,
      IsLocalRing.maximalIdeal_comap]
  have hne : q.comap (algebraMap R C) ≠ ⊥ := by
    intro h
    have he : q.comap (algebraMap A C) = ⊥ := by
      rw [IsScalarTower.algebraMap_eq A R C, ← Ideal.comap_comap, h]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A R)
    exact IsDiscreteValuationRing.not_a_field A (hA.symm.trans he)
  exact IsLocalRing.eq_maximalIdeal ((Ideal.IsPrime.comap (algebraMap R C)).isMaximal hne)

/-- The map to a prime localization is local when that prime contracts to the maximal ideal. -/
@[ega "I 8.1.1" "(i) ⇒ (ii)"]
theorem isLocalHom_localization_of_comap_eq_maximalIdeal
    (R C : Type*) [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C]
    (q : Ideal C) [q.IsPrime]
    (hq : q.comap (algebraMap R C) = maximalIdeal R) :
    IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
  rw [IsScalarTower.algebraMap_eq R C (Localization.AtPrime q), ← Ideal.comap_comap]
  show (Ideal.under C (maximalIdeal (Localization.AtPrime q))).comap (algebraMap R C) = _
  rw [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q, hq]

/-- The base acts faithfully on every prime localization of its integral closure in a field
algebra. -/
theorem faithfulSMul_integralClosure_localization
    (R K T : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [FaithfulSMul R K]
    [CommRing T] [Algebra K T] [Algebra R T] [IsScalarTower R K T]
    (q : Ideal (integralClosure R T)) [q.IsPrime] :
    FaithfulSMul R (Localization.AtPrime q) := by
  have : Nontrivial (integralClosure R T) := ⟨⟨0, 1, fun h =>
    (inferInstance : q.IsPrime).ne_top ((Ideal.eq_top_iff_one q).mpr (h ▸ q.zero_mem))⟩⟩
  have : Module.IsTorsionFree R T := Module.IsTorsionFree.trans_faithfulSMul R K T
  have : Module.IsTorsionFree R (integralClosure R T) := inferInstance
  have : Module.Flat R (integralClosure R T) := inferInstance
  have : Module.Flat R (Localization.AtPrime q) :=
    Module.Flat.trans R (integralClosure R T) (Localization.AtPrime q)
  have : Module.IsTorsionFree R (Localization.AtPrime q) := inferInstance
  exact Module.IsTorsionFree.to_faithfulSMul (R := R) (A := Localization.AtPrime q)

/-- Injectivity on the base implies injectivity on an integral intermediate domain. -/
theorem faithfulSMul_of_isIntegral_tower
    (A R S : Type*) [CommRing A] [Nontrivial A]
    [CommRing R] [IsDomain R] [Algebra A R] [Algebra.IsIntegral A R]
    [CommRing S] [Algebra A S] [FaithfulSMul A S]
    [Algebra R S] [IsScalarTower A R S] : FaithfulSMul R S := by
  apply (faithfulSMul_iff_algebraMap_injective R S).mpr
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply Ideal.eq_bot_of_comap_eq_bot (R := A)
  rw [RingHom.ker_eq_comap_bot, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A R S]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A S)

/-- Finite generation of a residue map is invariant under equality of the source prime. -/
theorem essFiniteType_residueField_map_of_eq
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p p' : Ideal R) (q : Ideal S) [p.IsPrime] [p'.IsPrime] [q.IsPrime]
    (hp : p = q.comap f) (hp' : p' = p)
    (h : (Ideal.ResidueField.map p q f hp).EssFiniteType) :
    (Ideal.ResidueField.map p' q f (hp'.trans hp)).EssFiniteType := by
  subst p'
  exact h

/-- Finite generation of residue fields is unchanged by localizing the source at its maximal
ideal. -/
theorem essFiniteType_residueField_of_localization
    (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime]
    [IsLocalHom (algebraMap R (Localization.AtPrime q))]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (h : (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R S) hq.symm).EssFiniteType) :
    Algebra.EssFiniteType (ResidueField R) q.ResidueField := by
  let g := Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R S) hq.symm
  have hf : (algebraMap (ResidueField R) (maximalIdeal R).ResidueField).EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R)).surjective).essFiniteType
  apply RingHom.essFiniteType_algebraMap.mp
  convert hf.comp h using 1
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := residue_surjective (R := R) x
  show (ResidueField.map (algebraMap R (Localization.AtPrime q))) (residue R a) =
    g (algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R a))
  rw [ResidueField.map_residue]
  show residue (Localization.AtPrime q) (algebraMap R (Localization.AtPrime q) a) =
    g (algebraMap R (maximalIdeal R).ResidueField a)
  rw [Ideal.ResidueField.map_algebraMap]
  show residue (Localization.AtPrime q) (algebraMap R (Localization.AtPrime q) a) =
    residue (Localization.AtPrime q)
      (algebraMap S (Localization.AtPrime q) (algebraMap R S a))
  rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q)]

/-- Finitely many finite field extensions embed in a common finite field extension. -/
private theorem exists_finite_common_extension
    (K : Type uK) [Field K] {ι : Type v} [Finite ι]
    (F : ι → Type uK) [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    [∀ i, Module.Finite K (F i)] :
    ∃ (E : Type uK) (_ : Field E) (_ : Algebra K E) (_ : Module.Finite K E),
      Nonempty (∀ i, F i →ₐ[K] E) := by
  let f (i : ι) : F i →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let T : IntermediateField K (AlgebraicClosure K) := ⨆ i, (f i).fieldRange
  have (i : ι) : Module.Finite K (f i).fieldRange :=
    Module.Finite.equiv (f i).equivFieldRange.toLinearEquiv
  have : Module.Finite K T := IntermediateField.finiteDimensional_iSup_of_finite
  refine ⟨T, inferInstance, inferInstance, inferInstance, ⟨fun i => ?_⟩⟩
  exact (IntermediateField.inclusion (le_iSup (fun i => (f i).fieldRange) i)).comp
    (f i).equivFieldRange.toAlgHom
/-- A finite family of solutions has a common finite extension which is a solution for every
member. -/
private theorem exists_finite_common_solution
    (A : Type uA) (K : Type uK) {ι : Type v} [Finite ι]
    (B : ι → Type uB) (L : ι → Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, IsDiscreteValuationRing (B i)] [∀ i, Field (L i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra A (L i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra K (L i)]
    [∀ i, IsScalarTower A (B i) (L i)] [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsDiscreteValuationRing.IsExtension A (B i)] [∀ i, IsFractionRing (B i) (L i)]
    (h : ∀ i, ∃ (F : Type uK) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
        max uL uK, uK, max uL uK} A (B i) K (L i) F,
        D.IsSolution.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK, max uL uK}) :
    ∃ (F : Type uK) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∀ i, ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
        max uL uK, uK, max uL uK} A (B i) K (L i) F,
        D.IsSolution.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK, max uL uK} := by
  classical
  choose F hF hKF hAF hAKF hfin hsol using h
  let (i : ι) : Field (F i) := hF i
  let (i : ι) : Algebra K (F i) := hKF i
  let (i : ι) : Algebra A (F i) := hAF i
  have (i : ι) : IsScalarTower A K (F i) := hAKF i
  have (i : ι) : Module.Finite K (F i) := hfin i
  obtain ⟨E, hE, hKE, hfinite, ⟨emb⟩⟩ := exists_finite_common_extension K F
  let : Field E := hE
  let : Algebra K E := hKE
  have : Module.Finite K E := hfinite
  let : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  let : Algebra (F i) E := (emb i).toAlgebra
  have : IsScalarTower K (F i) E :=
    IsScalarTower.of_algebraMap_eq' (emb i).comp_algebraMap.symm
  have : IsScalarTower A (F i) E := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap K E (algebraMap A K a) = emb i (algebraMap A (F i) a)
    rw [IsScalarTower.algebraMap_apply A K (F i), AlgHom.commutes]
  have : Module.Finite (F i) E := Module.Finite.of_restrictScalars_finite K (F i) E
  exact IsDiscreteValuationRing.exists_isSolution_of_tower A (B i) K (L i) (F i) E (hsol i)

/-- Local solutions over a perfect residue field share a finite common extension. -/
theorem exists_finite_extension_localSolutions_of_perfectField
    (A : Type uA) (K : Type uK) (C : Type uB)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [PerfectField (ResidueField A)]
    [CommRing C] [Algebra A C] [Finite (MaximalSpectrum C)]
    [∀ q : MaximalSpectrum C, IsDomain (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum C, IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum C,
      IsDiscreteValuationRing.IsExtension A (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum C,
      Algebra.EssFiniteType (ResidueField A) q.asIdeal.ResidueField]
    (hEpp : EppTheorem.{uA, uB, uK, uB}) :
    let B (q : MaximalSpectrum C) := Localization.AtPrime q.asIdeal
    let M (q : MaximalSpectrum C) := FractionRing (B q)
    ∃ (_ : ∀ q, Algebra K (M q)) (_ : ∀ q, IsScalarTower A K (M q))
      (F : Type uK) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∀ q, ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uB, uK,
        max uB uK, uK, max uB uK} A (B q) K (M q) F,
        D.IsSolution.{uA, uB, uK, uB, uK, max uB uK, uK, max uB uK,
          max uB uK} := by
  classical
  dsimp only
  let B (q : MaximalSpectrum C) := Localization.AtPrime q.asIdeal
  let M (q : MaximalSpectrum C) := FractionRing (B q)
  let (q : MaximalSpectrum C) : Field (M q) := FractionRing.field (B q)
  let (q : MaximalSpectrum C) : Algebra (B q) (M q) := inferInstance
  let (q : MaximalSpectrum C) : Algebra A (B q) := inferInstance
  let (q : MaximalSpectrum C) : Algebra A (M q) := inferInstance
  have (q : MaximalSpectrum C) : IsScalarTower A (B q) (M q) := inferInstance
  have (q : MaximalSpectrum C) : IsFractionRing (B q) (M q) := inferInstance
  have hmap (q : MaximalSpectrum C) : Function.Injective (algebraMap A (M q)) := by
    rw [IsScalarTower.algebraMap_eq A (B q) (M q)]
    exact (IsFractionRing.injective (B q) (M q)).comp
      (FaithfulSMul.algebraMap_injective A (B q))
  let (q : MaximalSpectrum C) : Algebra K (M q) :=
    (IsFractionRing.lift (K := K) (hmap q)).toAlgebra
  have (q : MaximalSpectrum C) : IsScalarTower A K (M q) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (IsFractionRing.lift_algebraMap (K := K) (hmap q) a).symm
  refine ⟨inferInstance, inferInstance, ?_⟩
  apply exists_finite_common_solution A K B M
  intro q
  exact exists_finite_extension_isSolution_of_perfectField A (B q) K (M q) hEpp

/-- Normalizing above an integral intermediate curve preserves the Dedekind property. -/
theorem isDedekindDomain_integralClosure_of_integral_base
    (A R K F : Type*) [CommRing A]
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]
    [Algebra A R] [Algebra.IsIntegral A R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field F] [Algebra K F] [Module.Finite K F]
    [Algebra R F] [IsScalarTower R K F]
    [Algebra A F] [IsScalarTower A R F] :
    IsDedekindDomain (integralClosure A F) := by
  let C := integralClosure A F
  let f : R →ₐ[A] C := IsIntegralClosure.lift A C F
  let : Algebra R C := f.toAlgebra
  have : IsScalarTower R C F := IsScalarTower.of_algebraMap_eq fun r =>
    (IsIntegralClosure.algebraMap_lift (A := C) A F r).symm
  have : IsIntegralClosure C R F := IsIntegralClosure.tower_top (R := A) (A := R)
  exact (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
    R K F C).1

end Stacks.EliminateRamification
