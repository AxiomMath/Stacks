module

public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.RingTheory.QuotSMulTop
public import StacksCore.Algebra.Homology.HomologicalComplexAbelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.LocalOrder
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.SupportLength
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Additivity
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Defs
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Length

/-!
# Multiplicity of multiplication on a one-dimensional module

For a finite module of support dimension at most one over a Noetherian local ring, the
multiplicity of the two-periodic complex with differentials zero and multiplication by an
element is a sum of orders of vanishing weighted by the lengths at the nonclosed points of the
support.

## Main results

* `AlgebraicGeometry.periodicLength_mul_eq_finsum_support` is the length-multiplication formula.
* `AlgebraicGeometry.periodicLength_mul_eq_length_quotSMulTop` is the regular case, where the
  multiplicity is the length of the quotient by the element.

## Implementation notes

The complex is `AlgebraicGeometry.twoPeriodicComplex`: its degree-zero differential is zero and
its degree-one differential is multiplication by `x`. Thus its degree-zero cohomology is
`M / xM` and its degree-one cohomology is the kernel of multiplication by `x`, in accordance
with the ordering `e_R(M, 0, x)` in the source. The displayed finite sum is represented by a
restricted `finsum` over the support with the closed point removed. Orders and module lengths
take values in `ℕ∞`; their finite values are mapped to integers using `ENat.toNat`.

The formula is proved by induction over a filtration of the module whose graded pieces are
residue rings of primes, using additivity of both sides on short exact sequences.

## References

* [Stacks Project, Tag 02QF](https://stacks.math.columbia.edu/tag/02QF)
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators
open scoped Pointwise

universe u v

namespace AlgebraicGeometry

/-- The support of the kernel of multiplication by `x` is contained in the support of the
quotient by `x`. -/
private lemma support_ker_mul_subset_quot
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) :
    Module.support R (LinearMap.ker (LinearMap.lsmul R M x)) ⊆
      Module.support R (QuotSMulTop x M) := by
  intro q hq
  rw [Module.support_quotSMulTop]
  refine ⟨Module.support_subset_of_injective
      (LinearMap.ker (LinearMap.lsmul R M x)).subtype Subtype.coe_injective hq, ?_⟩
  rintro _ rfl
  exact Module.annihilator_le_of_mem_support hq
    (Module.mem_annihilator.mpr fun z => Subtype.ext (LinearMap.mem_ker.mp z.property))

/-- If the quotient by `x` has zero-dimensional support, the kernel of multiplication by `x`
has finite length. -/
private lemma finite_length_ker_mul
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hxM : Module.supportDim R (QuotSMulTop x M) ≤ 0) :
    IsFiniteLength R (LinearMap.ker (LinearMap.lsmul R M x)) :=
  finite_length_of_supportDim_le_zero <| (Order.krullDim_le_of_strictMono
      (fun p : Module.support R (LinearMap.ker (LinearMap.lsmul R M x)) =>
        (⟨p.val, support_ker_mul_subset_quot x p.property⟩ :
          Module.support R (QuotSMulTop x M)))
      (fun _ _ h => h)).trans hxM

/-- The degree-zero cohomology of the two-periodic complex with differentials zero and
multiplication by `x` is the quotient by `x`. -/
private noncomputable def homology_zero_mul_equiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : R) :
    (twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
        (zero_mul _) (mul_zero _)).homology 0 ≃ₗ[R] QuotSMulTop x M := by
  let K := twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
        (zero_mul _) (mul_zero _)
  let S₀ := K.sc' 1 0 1
  have hg : S₀.g = 0 := by
    simp [S₀, K, HomologicalComplex.sc', twoPeriodicComplex]; rfl
  have hf : S₀.f.hom = LinearMap.lsmul R M x := by
    simp [S₀, K, HomologicalComplex.sc', twoPeriodicComplex]; rfl
  let e0 := K.homologyIsoSc' (1 : ZMod 2) 0 1 (by simp) (by simp) ≪≫
    S₀.asIsoHomologyι hg ≪≫ S₀.moduleCatOpcyclesIso
  exact e0.toLinearEquiv.trans
    (Submodule.quotEquivOfEq (LinearMap.range S₀.f.hom) _
      (by rw [hf]; exact range_lsmul_eq_smul_top x))

/-- The degree-one cohomology of the two-periodic complex with differentials zero and
multiplication by `x` is a quotient of the kernel of multiplication by `x`. -/
private lemma exists_surjective_ker_mul_homology_one
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : R) :
    ∃ f : LinearMap.ker (LinearMap.lsmul R M x) →ₗ[R]
        (twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
          (zero_mul _) (mul_zero _)).homology 1, Function.Surjective f := by
  let K := twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
        (zero_mul _) (mul_zero _)
  let S₁ := K.sc' 0 1 0
  have htwo : (1 + 1 : ZMod 2) = 0 := by decide
  have hg : S₁.g.hom = LinearMap.lsmul R M x := by
    simp [S₁, K, HomologicalComplex.sc', twoPeriodicComplex, htwo]; rfl
  let e1 := K.homologyIsoSc' (0 : ZMod 2) 1 0 (by simp) (by simp [htwo]) ≪≫
    S₁.moduleCatHomologyIso
  let q : LinearMap.ker S₁.g.hom →ₗ[R] S₁.moduleCatLeftHomologyData.H :=
    Submodule.mkQ (LinearMap.range S₁.moduleCatToCycles)
  let e : LinearMap.ker (LinearMap.lsmul R M x) ≃ₗ[R] LinearMap.ker S₁.g.hom :=
    LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hg).symm
  exact ⟨(e1.symm.toLinearEquiv : _ →ₗ[R] _) ∘ₗ q ∘ₗ (e : _ →ₗ[R] _),
    e1.symm.toLinearEquiv.surjective.comp
      ((Submodule.mkQ_surjective _).comp e.surjective)⟩

/-- If the quotient by `x` has zero-dimensional support, the two-periodic complex with
differentials zero and multiplication by `x` has finite-length cohomology. -/
private lemma finite_length_homology_mul
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hxM : Module.supportDim R (QuotSMulTop x M) ≤ 0) :
    HasFiniteLengthHomology
      (twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
        (zero_mul _) (mul_zero _)) := by
  obtain ⟨f, hf⟩ := exists_surjective_ker_mul_homology_one (M := M) x
  intro i
  fin_cases i
  · exact (homology_zero_mul_equiv x).symm.isFiniteLength
      (finite_length_of_supportDim_le_zero hxM)
  · exact (finite_length_ker_mul x hxM).of_surjective hf

/-- For a module of finite length, the two-periodic complex with differentials zero and
multiplication by `x` has periodic length zero. -/
private lemma periodicLength_mul_eq_zero_of_finiteLength
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x : R) (hM : IsFiniteLength R M) :
    periodicLength
        (twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
          (zero_mul _) (mul_zero _)) = 0 :=
  periodicLength_eq_zero_of_iso _ hM (Iso.refl _)

/-- When `x` acts regularly, the periodic length of the complex with differentials zero and
multiplication by `x` is the length of the quotient by `x`. -/
public lemma periodicLength_mul_eq_length_quotSMulTop {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (x : R)
    (hx : IsSMulRegular M x) :
    periodicLength
      (twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
        (zero_mul _) (mul_zero _)) = ((Module.length R (QuotSMulTop x M)).toNat : ℤ) := by
  obtain ⟨f, hf⟩ := exists_surjective_ker_mul_homology_one (M := M) x
  have hker : LinearMap.ker (LinearMap.lsmul R M x) = ⊥ := LinearMap.ker_eq_bot.mpr hx
  have : Subsingleton (LinearMap.ker (LinearMap.lsmul R M x)) := by
    rw [hker]
    infer_instance
  have := hf.subsingleton
  have h1 := Module.length_eq_zero (R := R) (M := (twoPeriodicComplex (0 : Module.End R M)
    (LinearMap.lsmul R M x) (zero_mul _) (mul_zero _)).homology 1)
  change ((Module.length R _).toNat : ℤ) - ((Module.length R _).toNat : ℤ) = _
  rw [h1, (homology_zero_mul_equiv x).length_eq]
  simp

/-- An element outside a prime acts regularly on the residue ring of that prime. -/
private lemma regular_quotientPrime
    {R : Type*} [CommRing R] (q : PrimeSpectrum R) (x : R)
    (hx : x ∉ q.asIdeal) : IsSMulRegular (R ⧸ q.asIdeal) x := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro a ha
  have hx0 : (Ideal.Quotient.mk q.asIdeal x : R ⧸ q.asIdeal) ≠ 0 :=
    fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h)
  change (Ideal.Quotient.mk q.asIdeal x) * a = 0 at ha
  exact (mul_eq_zero.mp ha).resolve_left hx0

/-- On the residue ring of a prime not containing `x`, the periodic length of multiplication
by `x` is the order of vanishing of `x`. -/
private lemma periodicLength_quotientPrime_eq_order
    {R : Type*} [CommRing R] (q : PrimeSpectrum R) (x : R) (hx : x ∉ q.asIdeal) :
    periodicLength
        (twoPeriodicComplex (0 : Module.End R (R ⧸ q.asIdeal))
          (LinearMap.lsmul R (R ⧸ q.asIdeal) x) (zero_mul _) (mul_zero _)) =
      ((Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x)).toNat : ℤ) := by
  rw [periodicLength_mul_eq_length_quotSMulTop x (regular_quotientPrime q x hx),
    (quotSMulTopQuotientEquiv x q.asIdeal).length_eq, ← ord_quotient_eq_length]

/-- A linear map between modules induces a morphism between the two-periodic complexes with
differentials zero and multiplication by `x`. -/
private noncomputable def multiplicationComplexMap
    {R : Type u} {M N : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (x : R) (f : M →ₗ[R] N) :
    (twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
        (zero_mul _) (mul_zero _)) ⟶
      (twoPeriodicComplex (0 : Module.End R N) (LinearMap.lsmul R N x)
        (zero_mul _) (mul_zero _)) where
  f _ := ModuleCat.ofHom f
  comm' i j hij := by
    have htwo : (1 + 1 : ZMod 2) = 0 := by decide
    have hcomm : (LinearMap.lsmul R N x).comp f =
        f.comp (LinearMap.lsmul R M x) :=
      LinearMap.ext fun z => (map_smul f x z).symm
    fin_cases i <;> fin_cases j <;>
      ext y <;> simp only [twoPeriodicComplex] <;>
        split_ifs <;> first | exact LinearMap.congr_fun hcomm y | simp

/-- The periodic length of multiplication by `x` is additive on a short exact sequence of
modules. -/
private lemma periodicLength_mul_additive_of_exact
    {R : Type u} {M₁ M₂ M₃ : Type v} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (x : R) (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g)
    (hfin : (HasFiniteLengthHomology
        (twoPeriodicComplex (0 : Module.End R M₁)
          (LinearMap.lsmul R M₁ x) (zero_mul _) (mul_zero _)) ∧
      HasFiniteLengthHomology
        (twoPeriodicComplex (0 : Module.End R M₂)
          (LinearMap.lsmul R M₂ x) (zero_mul _) (mul_zero _))) ∨
      (HasFiniteLengthHomology
        (twoPeriodicComplex (0 : Module.End R M₁)
          (LinearMap.lsmul R M₁ x) (zero_mul _) (mul_zero _)) ∧
      HasFiniteLengthHomology
        (twoPeriodicComplex (0 : Module.End R M₃)
          (LinearMap.lsmul R M₃ x) (zero_mul _) (mul_zero _))) ∨
      (HasFiniteLengthHomology
        (twoPeriodicComplex (0 : Module.End R M₂)
          (LinearMap.lsmul R M₂ x) (zero_mul _) (mul_zero _)) ∧
      HasFiniteLengthHomology
        (twoPeriodicComplex (0 : Module.End R M₃)
          (LinearMap.lsmul R M₃ x) (zero_mul _) (mul_zero _)))) :
    periodicLength
        (twoPeriodicComplex (0 : Module.End R M₂)
          (LinearMap.lsmul R M₂ x) (zero_mul _) (mul_zero _)) =
      periodicLength
        (twoPeriodicComplex (0 : Module.End R M₁)
          (LinearMap.lsmul R M₁ x) (zero_mul _) (mul_zero _)) +
      periodicLength
        (twoPeriodicComplex (0 : Module.End R M₃)
          (LinearMap.lsmul R M₃ x) (zero_mul _) (mul_zero _)) := by
  let S := ShortComplex.mk (multiplicationComplexMap x f)
    (multiplicationComplexMap x g) (by
      ext i y
      show g (f y) = 0
      exact LinearMap.congr_fun hfg.linearMap_comp_eq_zero y)
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S
    fun _ => ModuleCat.shortComplex_shortExact _ hfg hf hg
  exact periodicLength_additive_of_shortExact S hS hfin

/-- A prime lies in the support of its own residue ring. -/
private lemma mem_support_quotient {R : Type*} [CommRing R] (q : PrimeSpectrum R) :
    q ∈ Module.support R (R ⧸ q.asIdeal) := by
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  exact le_refl q.asIdeal

/-- The support of the residue ring at the closed point is the closed point. -/
private lemma support_quotient_closedPoint {R : Type*} [CommRing R] [IsLocalRing R] :
    Module.support R (R ⧸ (IsLocalRing.closedPoint R).asIdeal) = {IsLocalRing.closedPoint R} := by
  have : (IsLocalRing.closedPoint R).asIdeal.IsMaximal := by
    show (IsLocalRing.maximalIdeal R).IsMaximal
    infer_instance
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient,
    PrimeSpectrum.zeroLocus_eq_singleton]

/-- If the quotient of the residue ring of a nonclosed point by `x` has zero-dimensional
support, then `x` is not in that point. -/
private lemma not_mem_prime_of_quot_supportDim_le_zero
    {R : Type*} [CommRing R] [IsLocalRing R]
    (q : PrimeSpectrum R) (x : R)
    (hxM : Module.supportDim R (QuotSMulTop x (R ⧸ q.asIdeal)) ≤ 0)
    (hne : q ≠ IsLocalRing.closedPoint R) : x ∉ q.asIdeal := by
  intro hx
  have hq := mem_support_quotient q
  have hq' : q ∈ Module.support R (QuotSMulTop x (R ⧸ q.asIdeal)) := by
    rw [Module.support_quotSMulTop]
    exact ⟨hq, fun _ hy => Set.mem_singleton_iff.mp hy ▸ hx⟩
  exact hne (eq_closed_of_mem_supportDim_le_zero hxM q hq')

/-- The residue field at the closed point has finite length as a module over the ring. -/
private lemma finiteLength_quotient_closedPoint
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (q : PrimeSpectrum R) (hq : q = IsLocalRing.closedPoint R) :
    IsFiniteLength R (R ⧸ q.asIdeal) := by
  subst q
  apply isFiniteLength_of_support
  rw [support_quotient_closedPoint]

/-- For a residue ring of a prime, the periodic length of multiplication by `x` is the
restricted sum of the local contributions. -/
private lemma periodicLength_quotientPrime_eq_localOrderFinsum
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (q : PrimeSpectrum R) (x : R)
    (hM : Module.supportDim R (R ⧸ q.asIdeal) ≤ 1)
    (hxM : Module.supportDim R (QuotSMulTop x (R ⧸ q.asIdeal)) ≤ 0) :
    periodicLength
        (twoPeriodicComplex (0 : Module.End R (R ⧸ q.asIdeal))
          (LinearMap.lsmul R (R ⧸ q.asIdeal) x) (zero_mul _) (mul_zero _)) =
      ∑ᶠ r ∈ {r : PrimeSpectrum R |
          r ∈ Module.support R (R ⧸ q.asIdeal) ∧
            r ≠ IsLocalRing.closedPoint R},
        localOrderTerm (M := R ⧸ q.asIdeal) x r := by
  have hq := mem_support_quotient q
  by_cases hclosed : q = IsLocalRing.closedPoint R
  · have hsupp : Module.support R (R ⧸ q.asIdeal) = {IsLocalRing.closedPoint R} := by
      subst q
      exact support_quotient_closedPoint
    have hs : {r : PrimeSpectrum R | r ∈ Module.support R (R ⧸ q.asIdeal) ∧
        r ≠ IsLocalRing.closedPoint R} = ∅ := by
      ext r
      simp [hsupp]
    rw [hs, finsum_mem_empty]
    exact periodicLength_mul_eq_zero_of_finiteLength x
      (finiteLength_quotient_closedPoint q hclosed)
  · have hx := not_mem_prime_of_quot_supportDim_le_zero q x hxM hclosed
    have hs : {r : PrimeSpectrum R | r ∈ Module.support R (R ⧸ q.asIdeal) ∧
        r ≠ IsLocalRing.closedPoint R} = {q} := by
      ext r
      constructor
      · rintro ⟨hr, hne⟩
        have hqr : q ≤ r := by
          rwa [Module.support_eq_zeroLocus, Ideal.annihilator_quotient] at hr
        have hmin := minimal_of_mem_support_ne_closed hM r hr hne
        exact Set.mem_singleton_iff.mpr (le_antisymm (hmin.2 hq hqr) hqr)
      · rintro rfl
        exact ⟨hq, hclosed⟩
    rw [hs, finsum_mem_singleton, periodicLength_quotientPrime_eq_order q x hx]
    unfold localOrderTerm
    rw [localized_length_quotientPrime_eq_one]
    norm_num

/-- An isomorphism of modules induces an isomorphism of their quotients by `x`. -/
private noncomputable def quotSMulTopEquivOfLinearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (x : R) :
    QuotSMulTop x M ≃ₗ[R] QuotSMulTop x N := by
  let f := QuotSMulTop.map x e.toLinearMap
  let g := QuotSMulTop.map x e.symm.toLinearMap
  have hfg : g.comp f = LinearMap.id := by
    rw [← QuotSMulTop.map_comp]
    convert QuotSMulTop.map_id x M using 1
    ext a
    simp
  have hgf : f.comp g = LinearMap.id := by
    rw [← QuotSMulTop.map_comp]
    convert QuotSMulTop.map_id x N using 1
    ext a
    simp
  exact LinearEquiv.ofLinear f g hgf hfg

/-- A module isomorphic to the residue ring of a prime has the same periodic length for
multiplication by `x`. -/
private lemma periodicLength_mul_congr_quotientPrime
    {R N : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] (q : PrimeSpectrum R)
    (e : N ≃ₗ[R] R ⧸ q.asIdeal) (x : R)
    (hxQ : Module.supportDim R (QuotSMulTop x (R ⧸ q.asIdeal)) ≤ 0) :
    periodicLength
        (twoPeriodicComplex (0 : Module.End R N)
          (LinearMap.lsmul R N x) (zero_mul _) (mul_zero _)) =
      periodicLength
        (twoPeriodicComplex (0 : Module.End R (R ⧸ q.asIdeal))
          (LinearMap.lsmul R (R ⧸ q.asIdeal) x) (zero_mul _) (mul_zero _)) := by
  by_cases hclosed : q = IsLocalRing.closedPoint R
  · have hQ := finiteLength_quotient_closedPoint q hclosed
    have hN := e.symm.isFiniteLength hQ
    rw [periodicLength_mul_eq_zero_of_finiteLength x hN,
      periodicLength_mul_eq_zero_of_finiteLength x hQ]
  · have hx := not_mem_prime_of_quot_supportDim_le_zero q x hxQ hclosed
    have hregQ := regular_quotientPrime q x hx
    have hregN : IsSMulRegular N x := by
      intro a b hab
      apply e.injective
      apply hregQ
      simpa only [map_smul] using congrArg e hab
    rw [periodicLength_mul_eq_length_quotSMulTop x hregN,
      periodicLength_mul_eq_length_quotSMulTop x hregQ,
      (quotSMulTopEquivOfLinearEquiv e x).length_eq]

/-- **Stacks Project, Tag 02QF.** The multiplicity of the periodic complex `(M, 0, x)` is
the sum, over the nonclosed points in the support of `M`, of the order of `x` modulo that
point times the length of the localization of `M` there. -/
@[stacks 02QF]
public theorem periodicLength_mul_eq_finsum_support
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hM : Module.supportDim R M ≤ 1)
    (hxM : Module.supportDim R (QuotSMulTop x M) ≤ 0) :
    periodicLength
        (twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
          (zero_mul _) (mul_zero _)) =
      ∑ᶠ q ∈ {q : PrimeSpectrum R |
          q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        ((Ring.ord (R ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x)).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) := by
  classical
  show periodicLength
      (twoPeriodicComplex (0 : Module.End R M) (LinearMap.lsmul R M x)
        (zero_mul _) (mul_zero _)) =
    ∑ᶠ q ∈ {q : PrimeSpectrum R |
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
      localOrderTerm (M := M) x q
  revert x hM hxM
  induction ‹Module.Finite R M› using
      IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
      intro x hM hxM
      rw [periodicLength_mul_eq_zero_of_finiteLength x
        (IsFiniteLength.of_subsingleton : IsFiniteLength R N)]
      simp [Module.support_eq_empty]
  | quotient N q e =>
      intro x hM hxM
      have hqM : Module.supportDim R (R ⧸ q.asIdeal) ≤ 1 := by
        simpa only [Module.supportDim_eq_of_equiv e] using hM
      have hs : Module.support R (R ⧸ q.asIdeal) ⊆ Module.support R N := by
        rw [e.support_eq]
      have hqX : Module.supportDim R (QuotSMulTop x (R ⧸ q.asIdeal)) ≤ 0 :=
        (supportDim_quotSMulTop_le_of_support_subset x hs).trans hxM
      calc
        _ = periodicLength
            (twoPeriodicComplex (0 : Module.End R (R ⧸ q.asIdeal))
              (LinearMap.lsmul R (R ⧸ q.asIdeal) x) (zero_mul _) (mul_zero _)) :=
          periodicLength_mul_congr_quotientPrime q e x hqX
        _ = ∑ᶠ r ∈ {r : PrimeSpectrum R |
              r ∈ Module.support R (R ⧸ q.asIdeal) ∧
                r ≠ IsLocalRing.closedPoint R},
              localOrderTerm (M := R ⧸ q.asIdeal) x r :=
          periodicLength_quotientPrime_eq_localOrderFinsum q x hqM hqX
        _ = _ := (localOrderFinsum_congr x e).symm
  | exact N₁ N₂ N₃ f g hf hg hfg ih₁ ih₃ =>
      intro x hM hxM
      have hM₁ : Module.supportDim R N₁ ≤ 1 :=
        (Module.supportDim_le_of_injective f hf).trans hM
      have hM₃ : Module.supportDim R N₃ ≤ 1 :=
        (Module.supportDim_le_of_surjective g hg).trans hM
      have hx₁ : Module.supportDim R (QuotSMulTop x N₁) ≤ 0 :=
        (supportDim_quotSMulTop_le_of_support_subset x
          (Module.support_subset_of_injective f hf)).trans hxM
      have hx₃ : Module.supportDim R (QuotSMulTop x N₃) ≤ 0 :=
        (supportDim_quotSMulTop_le_of_support_subset x
          (Module.support_subset_of_surjective g hg)).trans hxM
      have hPL := periodicLength_mul_additive_of_exact x f g hf hg hfg
        (Or.inr (Or.inl ⟨finite_length_homology_mul x hx₁,
          finite_length_homology_mul x hx₃⟩))
      have hsum := localOrderFinsum_add_of_exact x hM f g hf hg hfg
      rw [hPL, hsum, ih₁ x hM₁ hx₁, ih₃ x hM₃ hx₃]

end AlgebraicGeometry
