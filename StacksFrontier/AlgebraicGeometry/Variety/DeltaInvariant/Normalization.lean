module

public import Mathlib.RingTheory.Length
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
public import StacksFrontier.RingTheory.IntegralClosure.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Nagata.IntegralClosure
public import StacksFrontier.RingTheory.Nagata.QuasiFinite
public import StacksFrontier.RingTheory.Noetherian.Spec
public import StacksFrontier.RingTheory.Support.Finite

/-!
# The integral closure of a one-dimensional reduced Nagata local ring

The integral closure of a reduced Nagata ring in its total ring of fractions is finite,
normal, and Nagata.  In the one-dimensional local case, its quotient by the original ring
has finite length.

## Main results

* `isNormalRing_integralClosure_fractionRing`: the integral closure of a reduced Noetherian
  ring is normal.
* `module_finite_integralClosure_fractionRing`: the integral closure is finite over the original
  ring.
* `isNagataRing_integralClosure_fractionRing`: the integral closure is Nagata.
* `isFiniteLength_integralClosure_quotient`: in the one-dimensional local case, the quotient by
  the original ring has finite length.

## References

* [Stacks Project, Tag 0C3S](https://stacks.math.columbia.edu/tag/0C3S)
-/

@[expose] public section

variable {A : Type*} [CommRing A]

/-- When the total ring of fractions is a localization away from a single element avoiding `p`,
the canonical map into the integral closure stays surjective after localizing at `p`. -/
private lemma localized_integralClosureMap_surjective
    (A : Type*) [CommRing A] [IsReduced A] {p : Ideal A} [p.IsPrime]
    {f : A} (hf : f ∉ p)
    (e : Localization.Away f ≃ₐ[A] FractionRing A) :
    Function.Surjective (LocalizedModule.map p.primeCompl
      (Algebra.linearMap A ↥(integralClosure A (FractionRing A)))) := by
  let C := ↥(integralClosure A (FractionRing A))
  let φ := Algebra.linearMap A C
  intro x
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl C) x
  obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.mk'_surjective (Submonoid.powers f)
    (e.symm c.1)
  have hrep : c.1 = e (IsLocalization.mk' (Localization.Away f) a t) := by
    simpa using (congrArg e ht).symm
  have hspec := congrArg e (IsLocalization.mk'_spec (Localization.Away f) a t)
  simp only [map_mul, ← hrep, AlgEquiv.commutes] at hspec
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff t.1 f).mp t.2
  rw [← hn] at hspec
  have hca : φ a = (f ^ n) • c := by
    apply Subtype.ext
    change algebraMap C (FractionRing A) (φ a) =
      algebraMap C (FractionRing A) ((f ^ n) • c)
    calc
      algebraMap C (FractionRing A) (φ a) = algebraMap A (FractionRing A) a := by
        simpa [φ] using
          (IsScalarTower.algebraMap_apply A C (FractionRing A) a).symm
      _ = algebraMap A (FractionRing A) (f ^ n) * c.1 := hspec.symm.trans (mul_comm _ _)
      _ = algebraMap C (FractionRing A) ((f ^ n) • c) := by
        rw [Algebra.smul_def, map_mul,
          IsScalarTower.algebraMap_apply A C (FractionRing A) (f ^ n)]
        rfl
  let s₀ : p.primeCompl := ⟨f ^ n, fun hmem => hf
    (Ideal.IsPrime.mem_of_pow_mem (inferInstance : p.IsPrime) n hmem)⟩
  refine ⟨IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl A) a (s₀ * s), ?_⟩
  change (IsLocalizedModule.map p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl A)
    (LocalizedModule.mkLinearMap p.primeCompl C) φ
      (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl A) a (s₀ * s))) = _
  rw [IsLocalizedModule.map_mk', hca]
  exact IsLocalizedModule.mk'_cancel_left
    (LocalizedModule.mkLinearMap p.primeCompl C) c s₀ s

/-- A finite integral closure of a reduced ring has the same support as the ring itself, and
hence the same support dimension. -/
private lemma integralClosure_faithful_supportDim
    {A : Type*} [CommRing A] [IsReduced A]
    (hfinite : Module.Finite A ↥(integralClosure A (FractionRing A))) :
    Module.support A ↥(integralClosure A (FractionRing A)) = Module.support A A ∧
      Module.supportDim A ↥(integralClosure A (FractionRing A)) = ringKrullDim A := by
  let C := ↥(integralClosure A (FractionRing A))
  let : Module.Finite A C := hfinite
  have hfaith : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr
    fun _ _ h => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val h)
  have hsuppC : Module.support A C = Module.support A A := by
    rw [Module.support_eq_zeroLocus, Module.annihilator_eq_bot.mpr hfaith,
      Module.support_eq_zeroLocus,
      Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul A A)]
  refine ⟨hsuppC, ?_⟩
  rw [← Module.supportDim_self_eq_ringKrullDim A]
  unfold Module.supportDim
  rw [hsuppC]

/-- In the one-dimensional local case the quotient of the integral closure by the ring is
supported at the closed point alone. -/
private lemma integralClosure_quotient_support_subset_closedPoint
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsReduced A]
    {f : A} (e : Localization.Away f ≃ₐ[A] FractionRing A)
    (havoid : ∀ p ∈ minimalPrimes A, f ∉ p)
    (hsuppC : Module.support A ↥(integralClosure A (FractionRing A)) =
      Module.support A A)
    (hdimC : Module.supportDim A ↥(integralClosure A (FractionRing A)) = 1) :
    Module.support A
      (↥(integralClosure A (FractionRing A)) ⧸
        LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A)))) ⊆
      {IsLocalRing.closedPoint A} := by
  let C := ↥(integralClosure A (FractionRing A))
  let φ := Algebra.linearMap A C
  let Q := C ⧸ LinearMap.range φ
  have hdimle : Order.krullDim (Module.support A C) ≤ 1 := by
    simpa [Module.supportDim] using hdimC.le
  have hfull (q : PrimeSpectrum A) : q ∈ Module.support A C := by
    rw [hsuppC, Module.support_eq_zeroLocus,
      Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul A A), PrimeSpectrum.zeroLocus_bot]
    exact Set.mem_univ q
  intro p hpQ
  have hpC : p ∈ Module.support A C :=
    Module.support_subset_of_surjective (Submodule.mkQ (LinearMap.range φ))
      (Submodule.mkQ_surjective _) hpQ
  rcases (Order.krullDim_le_one_iff.mp hdimle ⟨p, hpC⟩) with hmin | hmax
  · have hminSpec : IsMin p := fun q hqp =>
      (congrArg Subtype.val (hmin.eq_of_le (b := ⟨q, hfull q⟩) hqp)).ge
    have hpmin : p.asIdeal ∈ minimalPrimes A := PrimeSpectrum.isMin_iff.mp hminSpec
    have hsurj := localized_integralClosureMap_surjective A (havoid p.asIdeal hpmin) e
    exact absurd hpQ (Module.notMem_support_iff.mpr
      ((LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
        p.asIdeal.primeCompl φ).mp hsurj))
  · have hmaxSpec : IsMax p := fun q hpq =>
      (congrArg Subtype.val (hmax.eq_of_le (b := ⟨q, hfull q⟩) hpq)).ge
    exact Set.mem_singleton_iff.mpr
      (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (PrimeSpectrum.isMax_iff.mp hmaxSpec)))

/-- The integral closure of a reduced Noetherian ring in its total ring of fractions is a
normal ring. -/
@[stacks 0C3S "normality", ega "II 7.4.6" "affine case, 𝒜=R(X)"]
public lemma isNormalRing_integralClosure_fractionRing
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsReduced A] :
    IsNormalRing ↥(integralClosure A (FractionRing A)) := by
  have hmin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have hnil : nilradical A = ⊥ := by simp
  let eQ : (A ⧸ nilradical A) ≃ₐ[A] A :=
    (Ideal.quotientEquivAlgOfEq A hnil).trans (AlgEquiv.quotientBot A A)
  let : Algebra (A ⧸ nilradical A) (FractionRing A) :=
    ((algebraMap A (FractionRing A)).comp eQ.toRingEquiv.toRingHom).toAlgebra
  have : IsFractionRing (A ⧸ nilradical A) (FractionRing A) :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (S := FractionRing A)
      eQ.symm.toRingEquiv).mp (inferInstance : IsFractionRing A (FractionRing A))
  have : IsScalarTower A (A ⧸ nilradical A) (FractionRing A) :=
    .of_algebraMap_eq' (by
      ext x
      simp [RingHom.algebraMap_toAlgebra, eQ])
  let eK : FractionRing (A ⧸ nilradical A) ≃ₐ[A] FractionRing A :=
    (FractionRing.algEquiv (A ⧸ nilradical A) (FractionRing A)).restrictScalars A
  let e' : integralClosure A (FractionRing (A ⧸ nilradical A)) ≃ₐ[A]
      integralClosure A (FractionRing A) :=
    ((integralClosure A (FractionRing (A ⧸ nilradical A))).equivMapOfInjective
      eK.toAlgHom eK.injective).trans
      (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv eK))
  exact IsNormalRing.congr e'.toRingEquiv
    (isNormalRing_integralClosure_fractionRing_reduction A hmin)

/-- The integral closure of a reduced Nagata ring in its total ring of fractions is finite over
the original ring. -/
@[stacks 0C3S "finiteness", ega "IV 7.6.1" "more general"]
public lemma module_finite_integralClosure_fractionRing
    {A : Type*} [CommRing A] [IsReduced A]
    (hA : IsNagataRing A) :
    Module.Finite A ↥(integralClosure A (FractionRing A)) := by
  let : IsNoetherianRing A := hA.1
  let : IsIntegralClosure (integralClosure A (FractionRing A)) A (FractionRing A) :=
    integralClosure.isIntegralClosure A (FractionRing A)
  exact IsIntegralClosure.finite_of_essFiniteType_of_isReduced (S := FractionRing A) hA.2

/-- The integral closure of a reduced Nagata ring in its total ring of fractions is Nagata. -/
@[stacks 0C3S "Nagata", ega "IV 7.8.3" "(vii)"]
public lemma isNagataRing_integralClosure_fractionRing
    {A : Type*} [CommRing A] [IsReduced A]
    (hA : IsNagataRing A) :
    IsNagataRing ↥(integralClosure A (FractionRing A)) := by
  let : Module.Finite A ↥(integralClosure A (FractionRing A)) :=
    module_finite_integralClosure_fractionRing hA
  exact isNagataRing_of_quasiFinite hA

/-- For a reduced one-dimensional Nagata local ring, the quotient of its integral closure in
the total ring of fractions by the original ring has finite length. -/
@[stacks 0C3S "finite length",
  ega "IV 7.6.1" "finiteness of A' over A",
  ega "IV 7.8.3" "(vii), special case"]
public lemma isFiniteLength_integralClosure_quotient
    {A : Type*} [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) (hdim : ringKrullDim A = 1) :
    IsFiniteLength A
      (↥(integralClosure A (FractionRing A)) ⧸
        LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A)))) := by
  let : IsNoetherianRing A := hA.1
  let C := ↥(integralClosure A (FractionRing A))
  let φ := Algebra.linearMap A C
  let Q := C ⧸ LinearMap.range φ
  let : Module.Finite A C := module_finite_integralClosure_fractionRing hA
  let : Module.Finite A Q :=
    Module.Finite.quotient A (A := A) (M := C) (LinearMap.range φ)
  by_cases hQ : Subsingleton Q
  · exact IsFiniteLength.of_subsingleton
  let : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hQ
  obtain ⟨f, hf, hrad⟩ := IsLocalRing.exists_radical_span_eq_maximalIdeal hdim
  have havoid :=
    (IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes hdim hf).mp hrad
  have hdepth := IsLocalRing.depth_eq_one_of_isReduced hdim
  have hAway :=
    (IsLocalRing.notMem_minimalPrimes_iff_localizationAway_equiv_fractionRing_of_depth_eq_one
      hdim hdepth hf).mp havoid
  let e : Localization.Away f ≃ₐ[A] FractionRing A := Classical.choice hAway
  obtain ⟨hsuppC, hdimC'⟩ :=
    integralClosure_faithful_supportDim (A := A) inferInstance
  have hdimC : Module.supportDim A C = 1 := hdimC'.trans hdim
  have hsuppQ : Module.support A Q ⊆ {IsLocalRing.closedPoint A} :=
    integralClosure_quotient_support_subset_closedPoint e havoid hsuppC hdimC
  have hclosed : IsLocalRing.closedPoint A ∈ Module.support A Q :=
    IsLocalRing.closedPoint_mem_support A Q
  exact isFiniteLength_of_support (hsuppQ.antisymm (Set.singleton_subset_iff.mpr hclosed))
