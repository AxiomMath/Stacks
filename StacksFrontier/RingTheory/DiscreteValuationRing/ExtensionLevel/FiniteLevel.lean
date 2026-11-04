module

public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.LocalRing.ResidueSection
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.LevelDefinition
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.NonfieldKummer

open Stacks.DiscreteValuationRing.AdjoinPthRoot

/-!
# Making a degree-`p` extension have finite level

The finite, totally ramified base extension which is either a weak solution or makes a Galois
degree-`p` extension have finite level (Stacks Tag 09F4).
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u uA uK uL

open Polynomial


open scoped TensorProduct


namespace Stacks.DegreePExtensionLevel

set_option backward.isDefEq.respectTransparency false

private lemma adjoin_singleton_sub_div
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (y : L) (a b : K) (hb : b ≠ 0) :
    Algebra.adjoin K {(y - algebraMap K L a) / algebraMap K L b} =
      Algebra.adjoin K {y} := by
  apply le_antisymm
  · apply Algebra.adjoin_singleton_le
    rw [div_eq_mul_inv, ← map_inv₀]
    exact Subalgebra.mul_mem _
      (Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton y))
        (Subalgebra.algebraMap_mem _ a)) (Subalgebra.algebraMap_mem _ b⁻¹)
  · apply Algebra.adjoin_singleton_le
    have hb' : algebraMap K L b ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hb
    have hy : y = (y - algebraMap K L a) / algebraMap K L b *
        algebraMap K L b + algebraMap K L a := by
      rw [div_mul_cancel₀ _ hb', sub_add_cancel]
    have hm : (y - algebraMap K L a) / algebraMap K L b * algebraMap K L b +
        algebraMap K L a ∈ Algebra.adjoin K {(y - algebraMap K L a) / algebraMap K L b} :=
      Subalgebra.add_mem _
        (Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_singleton _))
          (Subalgebra.algebraMap_mem _ b)) (Subalgebra.algebraMap_mem _ a)
    rwa [← hy] at hm

private lemma wElt_ne_zero_of_charZero
    {A : Type*} [CommRing A] [CharZero A]
    {p : ℕ} [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* A) :
    wElt f ≠ 0 := by
  intro h
  have hz : zetaA f = 1 := (sub_eq_zero.mp h).symm
  have hp := zetaA_geom_sum_eq_zero f
  simp only [hz, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

private lemma exists_pow_eq_and_adjoin_eq_top_of_prime_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* K)
    (hdegree : Module.finrank K L = p) :
    ∃ (y : L) (b : K), y ^ p = algebraMap K L b ∧ Algebra.adjoin K {y} = ⊤ := by
  let ζ : K := zetaA f
  have hζpow : ζ ^ p = 1 := by
    dsimp [ζ, zetaA]
    rw [← map_pow]
    exact (congrArg f (IsCyclotomicExtension.zeta_spec p ℤ
      (CyclotomicRing p ℤ ℚ)).pow_eq_one).trans (map_one f)
  have hζne : ζ ≠ 1 := by
    intro h
    exact wElt_ne_zero_of_charZero f (sub_eq_zero.mpr h.symm)
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.mpr
    (orderOf_eq_prime hζpow hζne)
  let : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_of_prime_card ((IsGalois.card_aut_eq_finrank K L).trans hdegree)
  obtain ⟨y, ⟨b, hb⟩, hy⟩ := exists_root_adjoin_eq_top_of_isCyclic K L
    (by rw [hdegree]; exact ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩)
  refine ⟨y, b, ?_, ?_⟩
  · simpa only [hdegree] using hb.symm
  · have h := congrArg IntermediateField.toSubalgebra hy
    rwa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic y), IntermediateField.top_toSubalgebra] at h

private lemma wElt_comp
    {A B : Type*} [CommRing A] [CommRing B]
    {p : ℕ} [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* A) (g : A →+* B) :
    wElt (g.comp f) = g (wElt f) := by
  simp [wElt, zetaA]

private lemma intProp_map
    {A B : Type*} [CommRing A] [CommRing B]
    {p : ℕ} [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* A)
    (g : A →+* B) (P : Polynomial A) (hP : intProp f P) :
    intProp (g.comp f) (P.map g) := by
  have hw := wElt_comp f g
  refine ⟨?_, (Polynomial.natDegree_map_le).trans hP.2.1, ?_, ?_⟩
  · have h := congrArg (Polynomial.map g) hP.1
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_add, Polynomial.map_one, Polynomial.map_C, Polynomial.map_X, hw] using h
  · simp [hP.2.2.1]
  · intro i hi hip
    have h := congrArg g (hP.2.2.2 i hi hip)
    simpa only [hw, Polynomial.coeff_map, map_mul, map_pow, map_natCast] using h

private lemma isDegreePExtensionOfFiniteLevel_of_pow_eq_one_add
    {A K L : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L]
    [IsFractionRing A K] [Module.Finite K L] [CharZero A]
    (p : ℕ) [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* A)
    (P : Polynomial A) (hP : intProp f P)
    (hdegree : Module.finrank K L = p)
    (y : L) (hgen : Algebra.adjoin K {y} = ⊤)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (hy : y ^ p = 1 + algebraMap K L (algebraMap A K a)) :
    IsDegreePExtensionOfFiniteLevel A K L p f P := by
  let w : K := algebraMap A K (wElt f)
  have hw : w ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne (wElt_ne_zero_of_charZero f)
  have hwL : algebraMap K L w ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne hw
  let ξ : K := algebraMap A K a / w ^ p
  let z : L := (y - 1) / algebraMap K L w
  refine ⟨hdegree, ξ, z, ?_, ?_, a, ha, ?_⟩
  · simpa only [z, ← map_one (algebraMap K L), adjoin_singleton_sub_div y 1 w hw]
      using hgen
  · have hquot := congrArg
      (Polynomial.eval₂RingHom ((algebraMap K L).comp (algebraMap A K)) z) hP.1
    simp only [map_mul, map_pow, map_sub, map_add, map_one,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
      RingHom.comp_apply] at hquot
    change algebraMap K L w ^ p *
      Polynomial.eval₂ ((algebraMap K L).comp (algebraMap A K)) z P =
        (1 + algebraMap K L w * z) ^ p - 1 at hquot
    have hz : 1 + algebraMap K L w * z = y := by
      dsimp [z]
      rw [mul_div_cancel₀ _ hwL]
      ring
    rw [hz, hy, add_sub_cancel_left] at hquot
    apply mul_left_cancel₀ (pow_ne_zero p hwL)
    rw [hquot]
    dsimp [ξ]
    rw [map_div₀, map_pow, mul_div_cancel₀ _ (pow_ne_zero p hwL)]
  · dsimp [ξ]
    exact (mul_div_cancel₀ _ (pow_ne_zero p hw)).symm

private lemma isDegreePExtensionOfFiniteLevel_of_pow_eq_unit
    {A K L : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L]
    [IsFractionRing A K] [Module.Finite K L] [CharZero A]
    (p : ℕ) [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* A)
    (P : Polynomial A) (hP : intProp f P)
    (hdegree : Module.finrank K L = p)
    (y : L) (hgen : Algebra.adjoin K {y} = ⊤)
    (u : Aˣ) (hy : y ^ p = algebraMap K L (algebraMap A K u))
    (hres : ∃ r : IsLocalRing.ResidueField A, IsLocalRing.residue A u = r ^ p) :
    IsDegreePExtensionOfFiniteLevel A K L p f P := by
  obtain ⟨r, hr⟩ := hres
  obtain ⟨v, hv⟩ := IsLocalRing.residue_surjective r
  have hr0 : r ≠ 0 := by
    intro h
    have hu := (IsLocalRing.residue_ne_zero_iff_isUnit (u : A)).mpr u.isUnit
    rw [hr, h, zero_pow (Fact.out : p.Prime).ne_zero] at hu
    exact hu rfl
  have hvunit : IsUnit v :=
    (IsLocalRing.residue_ne_zero_iff_isUnit v).mp (hv ▸ hr0)
  obtain ⟨v, rfl⟩ := hvunit
  let a : A := (u : A) * (↑(v⁻¹) : A) ^ p - 1
  have ha : a ∈ IsLocalRing.maximalIdeal A := by
    apply (IsLocalRing.residue_eq_zero_iff a).mp
    dsimp [a]
    rw [map_sub, map_mul, map_pow, map_one, hr, ← hv, ← mul_pow]
    have hmul : IsLocalRing.residue A (v : A) *
        IsLocalRing.residue A (↑(v⁻¹) : A) = 1 := by
      simp
    rw [hmul, one_pow, sub_self]
  have hvK : algebraMap A K (v : A) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr v.ne_zero
  have hinv : algebraMap A K (↑(v⁻¹) : A) = (algebraMap A K (v : A))⁻¹ :=
    map_units_inv (algebraMap A K) v
  refine isDegreePExtensionOfFiniteLevel_of_pow_eq_one_add p f P hP hdegree
    (y / algebraMap K L (algebraMap A K (v : A))) ?_ a ha ?_
  · simpa only [map_zero, sub_zero] using
      (adjoin_singleton_sub_div y 0 (algebraMap A K (v : A)) hvK).trans hgen
  · rw [div_pow, hy]
    dsimp [a]
    simp only [map_sub, map_mul, map_pow, map_one, hinv, map_inv₀]
    rw [add_sub_cancel, div_eq_mul_inv, inv_pow]

private lemma exists_pow_eq_unit_of_pow_eq_unit_mul_zpow
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L]
    (p : ℕ) (y : L) (u : Aˣ) (π : K) (hπ : π ≠ 0) (n : ℤ)
    (hy : y ^ p = algebraMap K L (algebraMap A K u * π ^ n))
    (hn : (p : ℤ) ∣ n) :
    ∃ z : L, z ^ p = algebraMap K L (algebraMap A K u) ∧
      Algebra.adjoin K {z} = Algebra.adjoin K {y} := by
  obtain ⟨k, rfl⟩ := hn
  let z := y / algebraMap K L (π ^ k)
  have hπk : π ^ k ≠ 0 := zpow_ne_zero k hπ
  refine ⟨z, ?_, ?_⟩
  · have hp : π ^ ((p : ℤ) * k) = (π ^ k) ^ p := by
      rw [mul_comm, zpow_mul, zpow_natCast]
    dsimp [z]
    rw [div_pow, hy, hp, map_mul, map_pow]
    exact mul_div_cancel_right₀ _
      (pow_ne_zero p ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hπk))
  · simpa only [map_zero, sub_zero] using adjoin_singleton_sub_div y 0 (π ^ k) hπk

private lemma exists_pow_eq_unit_of_pow_eq_unit_mul_zpow_of_pow_eq
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L]
    (p : ℕ) (y : L) (u : Aˣ) (π t : K) (ht : t ≠ 0) (n : ℤ)
    (hy : y ^ p = algebraMap K L (algebraMap A K u * π ^ n))
    (hpow : t ^ p = π) :
    ∃ z : L, z ^ p = algebraMap K L (algebraMap A K u) ∧
      Algebra.adjoin K {z} = Algebra.adjoin K {y} := by
  have he : π ^ n = t ^ ((p : ℤ) * n) := by
    rw [← hpow, ← zpow_natCast, ← zpow_mul]
  rw [he] at hy
  exact exists_pow_eq_unit_of_pow_eq_unit_mul_zpow p y u t ht ((p : ℤ) * n) hy
    (dvd_mul_right _ _)

private lemma kummer_parameter_ne_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : ℕ) (hp : 1 < p) (y : L) (b : K)
    (hy : y ^ p = algebraMap K L b) (hgen : Algebra.adjoin K {y} = ⊤)
    (hdegree : Module.finrank K L = p) : b ≠ 0 := by
  intro hb
  have hy0 : y = 0 := (pow_eq_zero_iff (by omega : p ≠ 0)).mp (by rw [hy, hb, map_zero])
  have hbot : (⊥ : Subalgebra K L) = ⊤ := by
    simpa only [hy0, Algebra.adjoin_singleton_zero] using hgen
  have hsurj : Function.Surjective (algebraMap K L) := by
    intro z
    have hz : z ∈ (⊥ : Subalgebra K L) := by rw [hbot]; trivial
    exact hz
  have hdeg1 : Module.finrank K L = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨(algebraMap K L).injective, hsurj⟩
  omega

private lemma surjective_algebraMap_of_isFractionRing_of_isLocalHom
    (R S K : Type*) [CommRing R] [CommRing S] [Field K]
    [IsDomain R] [IsDomain S] [ValuationRing R]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K]
    [IsLocalHom (algebraMap R S)] :
    Function.Surjective (algebraMap R S) := by
  intro s
  by_cases hs : s = 0
  · exact ⟨0, by simp [hs]⟩
  have hsK : algebraMap S K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S K)).mpr hs
  obtain ⟨r, hr | hr⟩ := (ValuationRing.isFractionRing_iff.mp
    (inferInstance : IsFractionRing R K)).1 (algebraMap S K s)
  · refine ⟨r, IsFractionRing.injective S K ?_⟩
    rw [← IsScalarTower.algebraMap_apply R S K, hr]
  · have hmul : algebraMap R S r * s = 1 := by
      apply IsFractionRing.injective S K
      rw [map_mul, ← IsScalarTower.algebraMap_apply R S K, ← hr,
        inv_mul_cancel₀ hsK, map_one]
    have hunit : IsUnit r := isUnit_of_map_unit (algebraMap R S) r
      (IsUnit.of_mul_eq_one _ hmul)
    obtain ⟨u, rfl⟩ := hunit
    refine ⟨↑(u⁻¹), ?_⟩
    apply IsFractionRing.injective S K
    rw [← IsScalarTower.algebraMap_apply R S K]
    rw [map_units_inv (algebraMap R K) u, ← hr, inv_inv]

/-- **The integral closure in a totally ramified Kummer extension of prime degree is a discrete
valuation ring.**

Let `B` be a discrete valuation ring with fraction field `L`, let `M / L` have degree `p`, and
suppose `M` contains a `p`-th root `y` of `u * π ^ n` for a unit `u`, a uniformizer `π` and an
exponent `n` **not** divisible by `p`. Then `integralClosure B M` is again a discrete valuation
ring. -/
lemma isDiscreteValuationRing_integralClosure_of_pow_eq_unit_mul_zpow
    (B L M : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Field M] [Algebra B L] [Algebra L M] [Algebra B M]
    [IsScalarTower B L M] [IsFractionRing B L] [Module.Finite L M]
    (p : ℕ) [Fact p.Prime] (hdegree : Module.finrank L M = p)
    (π : B) (hπ : Irreducible π) (u : Bˣ) (n : ℤ)
    (y : M) (hy : y ^ p = algebraMap L M (algebraMap B L u * algebraMap B L π ^ n))
    (hn : ¬ (p : ℤ) ∣ n) :
    IsDiscreteValuationRing (integralClosure B M) := by
  have hc : IsCoprime (p : ℤ) n := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (mt Int.natCast_dvd.mpr hn)
  obtain ⟨a, b, hab⟩ := hc
  let π' : B := (↑(u ^ b) : B) * π
  have hπ' : Irreducible π' := (irreducible_isUnit_mul (u ^ b).isUnit).mpr hπ
  let x : M := y ^ b * algebraMap B M π ^ a
  have hπM : algebraMap B M π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply B L M]
    exact (map_ne_zero_iff _ (algebraMap L M).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hπ.ne_zero)
  have hx : x ^ p = algebraMap B M π' := by
    have hu : algebraMap B M (↑(u ^ b) : B) = algebraMap B M (u : B) ^ b :=
      ((algebraMap B M).toMonoidHom.comp (Units.coeHom B)).map_zpow u b
    have hy' : y ^ p = algebraMap B M (u : B) * algebraMap B M π ^ n := by
      simpa only [map_mul, map_zpow₀, ← IsScalarTower.algebraMap_apply B L M] using hy
    dsimp [x, π']
    rw [mul_pow, ← zpow_natCast (y ^ b) p, ← zpow_mul, mul_comm b (p : ℤ),
      zpow_mul, zpow_natCast, hy', mul_zpow, map_mul, hu]
    rw [← zpow_mul, ← zpow_natCast (algebraMap B M π ^ a) p, ← zpow_mul]
    rw [mul_assoc, ← zpow_add₀ hπM]
    have he : n * b + a * (p : ℤ) = 1 := by linarith [hab]
    rw [he, zpow_one]
  have hirr := Stacks.KummerExtension.kummerPoly_irreducible L π' p (Fact.out : p.Prime).one_lt.le
    hπ'
  let : Fact (Irreducible (Stacks.KummerExtension.kummerPoly L π' p)) := ⟨hirr⟩
  let E := Stacks.KummerExtension.K1 L π' p
  let g : E →ₐ[L] M := AdjoinRoot.liftAlgHom _ (Algebra.ofId L M) x (by
    simp only [Stacks.KummerExtension.kummerPoly, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    show x ^ p - algebraMap L M (algebraMap B L π') = 0
    rw [← IsScalarTower.algebraMap_apply B L M, hx, sub_self])
  have heq : Module.finrank L E = Module.finrank L M :=
    (Stacks.KummerExtension.finrank_K1 L π' p (Fact.out : p.Prime).two_le hπ').trans hdegree.symm
  let e : E ≃ₐ[L] M := AlgEquiv.ofBijective g ⟨g.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq
      (f := g.toLinearMap)).mp g.injective⟩
  let : IsDiscreteValuationRing (integralClosure B E) :=
    Stacks.KummerExtension.isDiscreteValuationRing_A1 L π' p (Fact.out : p.Prime).two_le hπ'
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (e.restrictScalars B).mapIntegralClosure

private lemma integralClosure_algEquiv_of_isDiscreteValuationRing
    (B C L M : Type*) [CommRing B] [CommRing C]
    [IsDomain B] [IsDomain C] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field L] [Field M] [Algebra B C] [Algebra B L] [Algebra C M]
    [Algebra B M] [Algebra L M] [IsScalarTower B C M] [IsScalarTower B L M]
    [IsFractionRing B L] [IsFractionRing C M] [Module.Finite L M]
    [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing (integralClosure B M)] :
    Nonempty (integralClosure B M ≃ₐ[B] C) := by
  let R := integralClosure B M
  let g : R →ₐ[B] C :=
    { toFun := fun x => IsIntegralClosure.mk' (R := C) C (x : M) (x.property.tower_top (A := C))
      map_zero' := by apply IsFractionRing.injective C M; simp
      map_one' := by apply IsFractionRing.injective C M; simp
      map_add' := by intro x y; apply IsFractionRing.injective C M; simp
      map_mul' := by intro x y; apply IsFractionRing.injective C M; simp
      commutes' := by
        intro b
        apply IsFractionRing.injective C M
        simp [← IsScalarTower.algebraMap_apply B C M] }
  have hg : ∀ x : R, algebraMap C M (g x) = (x : M) := by
    intro x
    exact IsIntegralClosure.algebraMap_mk' (R := C) C (x : M)
      (x.property.tower_top (A := C))
  let : Algebra R C := g.toRingHom.toAlgebra
  let : IsScalarTower R C M := IsScalarTower.of_algebraMap_eq (fun x => (hg x).symm)
  let : IsFractionRing R M := integralClosure.isFractionRing_of_finite_extension L M
  let J : Ideal R := (IsLocalRing.maximalIdeal C).comap g.toRingHom
  have hJprime : J.IsPrime := Ideal.comap_isPrime _ _
  have hJne : J ≠ ⊥ := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
    intro hJ
    have hm : algebraMap B R π ∈ J := by
      show g (algebraMap B R π) ∈ IsLocalRing.maximalIdeal C
      rw [g.commutes]
      exact fun h => hπ.not_isUnit (isUnit_of_map_unit (algebraMap B C) π h)
    rw [hJ, Ideal.mem_bot] at hm
    apply hπ.ne_zero
    apply FaithfulSMul.algebraMap_injective B C
    simpa only [g.commutes, map_zero] using congrArg g hm
  have hJ : J = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (hJprime.isMaximal hJne)
  let : IsLocalHom (algebraMap R C) := ⟨fun x hx => by
    by_contra hxu
    have hm : x ∈ J := hJ.symm ▸ hxu
    exact hm hx⟩
  have hsurj := surjective_algebraMap_of_isFractionRing_of_isLocalHom R C M
  refine ⟨AlgEquiv.ofBijective g ⟨?_, hsurj⟩⟩
  intro x y h
  exact Subtype.ext ((hg x).symm.trans ((congrArg (algebraMap C M) h).trans (hg y)))

private lemma exists_integralClosure_algEquiv_of_isIntegral
    (B C D T : Type*) [CommRing B] [CommRing C] [CommRing D] [CommRing T]
    [Algebra B C] [Algebra B D] [Algebra B T] [Algebra C T] [Algebra D T]
    [IsScalarTower B C T] [IsScalarTower B D T]
    [Algebra.IsIntegral B C] [Algebra.IsIntegral B D] :
    ∃ e : integralClosure C T ≃ₐ[B] integralClosure D T,
      ∀ x : integralClosure C T, (e x : T) = (x : T) := by
  refine ⟨Stacks.DiscreteValuationRing.AdjoinPthRoot.integralClosureEquivOfIsIntegral.trans
    (Stacks.DiscreteValuationRing.AdjoinPthRoot.integralClosureEquivOfIsIntegral (R := B) (S := D)
      (T := T)).symm, ?_⟩
  intro x
  rfl

private lemma isWeaklyUnramified_iff_irreducible_algebraMap
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    (π : A) (hπ : Irreducible π) :
    IsDiscreteValuationRing.IsWeaklyUnramified A B ↔ Irreducible (algebraMap A B π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  have hm : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      Ideal.span {algebraMap A B π} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.map_span, Set.image_singleton]
  constructor
  · intro h
    have he := (IsDiscreteValuationRing.ramificationIndex_characterization A B).2.1
    change IsDiscreteValuationRing.ramificationIndex A B = 1 at h
    rw [h, pow_one, hm] at he
    exact he.symm
  · intro h
    exact ((IsDiscreteValuationRing.ramificationIndex_characterization A B).2.2.1 1 le_rfl
      (by simpa only [pow_one, hm] using h.symm)).symm

private lemma isWeaklyUnramified_or_finiteLevel_of_pow_eq_unit
    (B C L M : Type u) [CommRing B] [CommRing C]
    [IsDomain B] [IsDomain C] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field L] [Field M] [Algebra B C] [Algebra B L] [Algebra C M]
    [Algebra B M] [Algebra L M] [IsScalarTower B C M] [IsScalarTower B L M]
    [IsFractionRing B L] [IsFractionRing C M] [Module.Finite L M] [CharZero B]
    [IsDiscreteValuationRing.IsExtension B C]
    (p : ℕ) [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* B)
    (P : Polynomial B) (hP : intProp f P) (hdegree : Module.finrank L M = p)
    (y : M) (hgen : Algebra.adjoin L {y} = ⊤)
    (u : Bˣ) (hy : y ^ p = algebraMap B M (u : B)) :
    IsDiscreteValuationRing.IsWeaklyUnramified B C ∨
      IsDegreePExtensionOfFiniteLevel B L M p f P := by
  by_cases hres : ∃ r : IsLocalRing.ResidueField B, IsLocalRing.residue B u = r ^ p
  · right
    apply isDegreePExtensionOfFiniteLevel_of_pow_eq_unit p f P hP hdegree y hgen u
      _ hres
    rwa [← IsScalarTower.algebraMap_apply B L M]
  · left
    obtain ⟨hclosure, hπclosure⟩ :=
      isDiscreteValuationRing_integralClosure_and_irreducible_of_pow_eq
        (K := L) p (u : B) hres y hy hgen
    let := hclosure
    obtain ⟨e⟩ := integralClosure_algEquiv_of_isDiscreteValuationRing B C L M
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
    apply (isWeaklyUnramified_iff_irreducible_algebraMap B C π hπ).mpr
    rw [← e.commutes π]
    exact (MulEquiv.irreducible_iff (f := e.toMulEquiv)).mpr (hπclosure π hπ)

private noncomputable def tensorProductMapEquiv
    (K L M E : Type*) [CommSemiring K] [CommSemiring L]
    [CommSemiring M] [CommSemiring E]
    [Algebra K L] [Algebra K M] [Algebra L M] [Algebra K E]
    [IsScalarTower K L M] :
    letI : Algebra (L ⊗[K] E) (M ⊗[K] E) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
        (AlgHom.id K E)).toRingHom.toAlgebra
    (L ⊗[K] E) ⊗[L] M ≃ₐ[L ⊗[K] E] M ⊗[K] E := by
  let ι := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K E)
  letI : Algebra (L ⊗[K] E) (M ⊗[K] E) := ι.toRingHom.toAlgebra
  let e := (Algebra.TensorProduct.comm L (L ⊗[K] E) M).trans
    (Algebra.TensorProduct.cancelBaseChange K L L M E)
  refine { __ := e.toRingEquiv, commutes' := ?_ }
  intro x
  change e (algebraMap (L ⊗[K] E) ((L ⊗[K] E) ⊗[L] M) x) = ι x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    change e ((l ⊗ₜ[K] a) ⊗ₜ[L] (1 : M)) = ι (l ⊗ₜ[K] a)
    simp [e, ι, Algebra.smul_def]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private lemma tensorProductMapEquiv_tmul
    (K L M E : Type*) [CommSemiring K] [CommSemiring L]
    [CommSemiring M] [CommSemiring E]
    [Algebra K L] [Algebra K M] [Algebra L M] [Algebra K E]
    [IsScalarTower K L M] (l : L) (a : E) (m : M) :
    tensorProductMapEquiv K L M E ((l ⊗ₜ[K] a) ⊗ₜ[L] m) = (l • m) ⊗ₜ[K] a := by
  simp [tensorProductMapEquiv]

/-- An algebra equivalence carries a generator of the whole algebra to a generator. -/
private lemma adjoin_singleton_algEquiv_eq_top
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (y : A) (hy : Algebra.adjoin R {y} = ⊤) :
    Algebra.adjoin R {e y} = ⊤ := by
  have h := congrArg (fun S : Subalgebra R A => S.map e.toAlgHom) hy
  rwa [AlgHom.map_adjoin_singleton, Algebra.map_top,
    (AlgHom.range_eq_top _).mpr e.surjective] at h

private lemma isScalarTower_tensorProduct_map
    (K L M E : Type*) [CommSemiring K] [CommSemiring L]
    [CommSemiring M] [CommSemiring E]
    [Algebra K L] [Algebra K M] [Algebra L M] [Algebra K E]
    [IsScalarTower K L M] :
    letI : Algebra (L ⊗[K] E) (M ⊗[K] E) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
        (AlgHom.id K E)).toRingHom.toAlgebra
    IsScalarTower L (L ⊗[K] E) (M ⊗[K] E) :=
  letI : Algebra (L ⊗[K] E) (M ⊗[K] E) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K E)).toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun l => by simp [RingHom.algebraMap_toAlgebra]

private lemma adjoin_tensorProduct_map_eq_top
    (K L M E : Type*) [CommSemiring K] [CommSemiring L]
    [CommSemiring M] [CommSemiring E]
    [Algebra K L] [Algebra K M] [Algebra L M] [Algebra K E]
    [IsScalarTower K L M] (y : M) (hy : Algebra.adjoin L {y} = ⊤) :
    letI : Algebra (L ⊗[K] E) (M ⊗[K] E) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
        (AlgHom.id K E)).toRingHom.toAlgebra
    Algebra.adjoin (L ⊗[K] E) {y ⊗ₜ[K] (1 : E)} = ⊤ := by
  let : Algebra (L ⊗[K] E) (M ⊗[K] E) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
      (AlgHom.id K E)).toRingHom.toAlgebra
  let e := tensorProductMapEquiv K L M E
  have hg : Algebra.adjoin (L ⊗[K] E) {(1 : L ⊗[K] E) ⊗ₜ[L] y} = ⊤ := by
    simpa only [Set.image_singleton] using
      (Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := L ⊗[K] E) {y} hy)
  have he := adjoin_singleton_algEquiv_eq_top e _ hg
  have hy' : e ((1 : L ⊗[K] E) ⊗ₜ[L] y) = y ⊗ₜ[K] (1 : E) := by
    show tensorProductMapEquiv K L M E ((1 ⊗ₜ[K] 1) ⊗ₜ[L] y) = _
    rw [tensorProductMapEquiv_tmul, one_smul]
  change Algebra.adjoin (L ⊗[K] E) {e ((1 : L ⊗[K] E) ⊗ₜ[L] y)} = ⊤ at he
  rwa [hy'] at he

private lemma finite_finrank_tensorProduct_map
    (K L M E : Type*) [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra L M] [Algebra K E]
    [IsScalarTower K L M] [Module.Finite L M]
    (hL₁ : IsField (L ⊗[K] E)) :
    letI := hL₁.toField
    letI : Algebra (L ⊗[K] E) (M ⊗[K] E) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
        (AlgHom.id K E)).toRingHom.toAlgebra
    Module.Finite (L ⊗[K] E) (M ⊗[K] E) ∧
      Module.finrank (L ⊗[K] E) (M ⊗[K] E) = Module.finrank L M := by
  let := hL₁.toField
  let : Algebra (L ⊗[K] E) (M ⊗[K] E) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
      (AlgHom.id K E)).toRingHom.toAlgebra
  let e := tensorProductMapEquiv K L M E
  refine ⟨Module.Finite.equiv e.toLinearEquiv, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_baseChange]

private lemma exists_pow_eq_unit_tensorProduct_of_pow_eq
    (B K L M E : Type u) [CommRing B]
    [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra K M] [Algebra L M] [Algebra K E]
    [IsScalarTower K L M] [Algebra B L]
    (p : ℕ) (hp : p ≠ 0) (π : K) (hπ : π ≠ 0) (y : M) (u : Bˣ) (n : ℤ)
    (hy : y ^ p = algebraMap L M
      (algebraMap B L u * algebraMap K L π ^ n))
    (hgen : Algebra.adjoin L {y} = ⊤)
    (t : E) (ht : t ^ p = algebraMap K E π)
    (hL₁ : IsField (L ⊗[K] E)) (hM₁ : IsField (M ⊗[K] E)) :
    letI := hL₁.toField
    letI := hM₁.toField
    letI : Algebra (L ⊗[K] E) (M ⊗[K] E) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
        (AlgHom.id K E)).toRingHom.toAlgebra
    ∃ z : M ⊗[K] E,
      z ^ p = algebraMap (L ⊗[K] E) (M ⊗[K] E) (algebraMap B (L ⊗[K] E) u) ∧
        Algebra.adjoin (L ⊗[K] E) {z} = ⊤ := by
  let := hL₁.toField
  let := hM₁.toField
  let L₁ := L ⊗[K] E
  let M₁ := M ⊗[K] E
  let ι := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K E)
  let : Algebra L₁ M₁ := ι.toRingHom.toAlgebra
  let : IsScalarTower L L₁ M₁ := isScalarTower_tensorProduct_map K L M E
  let t₁ : L₁ := (Algebra.TensorProduct.includeRight : E →ₐ[K] L₁) t
  have ht₁ : t₁ ^ p = algebraMap L L₁ (algebraMap K L π) := by
    show ((Algebra.TensorProduct.includeRight : E →ₐ[K] L₁) t) ^ p = _
    rw [← map_pow, ht, AlgHom.commutes, ← IsScalarTower.algebraMap_apply K L L₁]
  have ht₁ne : t₁ ≠ 0 := by
    intro h
    have hπ₁ : algebraMap L L₁ (algebraMap K L π) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap L L₁).injective).mpr
        ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hπ)
    exact hπ₁ (by rw [← ht₁, h, zero_pow hp])
  have hy₁ : (algebraMap M M₁ y) ^ p = algebraMap L₁ M₁
      (algebraMap B L₁ u * algebraMap L L₁ (algebraMap K L π) ^ n) := by
    rw [← map_pow, hy, ← IsScalarTower.algebraMap_apply L M M₁,
      IsScalarTower.algebraMap_apply L L₁ M₁]
    simp only [map_mul, map_zpow₀, ← IsScalarTower.algebraMap_apply B L L₁]
  obtain ⟨z, hz, hzg⟩ := exists_pow_eq_unit_of_pow_eq_unit_mul_zpow_of_pow_eq p
    (algebraMap M M₁ y) u (algebraMap L L₁ (algebraMap K L π)) t₁ ht₁ne n hy₁ ht₁
  refine ⟨z, hz, hzg.trans ?_⟩
  exact adjoin_tensorProduct_map_eq_top K L M E y hgen

private lemma finiteLevel_tensorProduct_self
    (B K L M : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Algebra B L] [IsFractionRing B L] [Module.Finite L M]
    (p : ℕ) [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* B)
    (P : Polynomial B) (hlevel : IsDegreePExtensionOfFiniteLevel B L M p f P) :
    let L₁ := L ⊗[K] K
    let M₁ := M ⊗[K] K
    ∃ (hL₁ : IsField L₁) (hM₁ : IsField M₁),
      letI := hL₁.toField
      letI := hM₁.toField
      let ι : L₁ →ₐ[K] M₁ :=
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K K)
      letI : Algebra L₁ M₁ := ι.toRingHom.toAlgebra
      let B₁ := integralClosure B L₁
      ∃ (hB₁ : IsDiscreteValuationRing B₁) (hfrac : IsFractionRing B₁ L₁)
        (hfin : Module.Finite L₁ M₁),
        letI := hB₁
        letI := hfrac
        letI := hfin
        IsDegreePExtensionOfFiniteLevel B₁ L₁ M₁ p
          ((algebraMap B B₁).comp f) (P.map (algebraMap B B₁)) := by
  let L₁ := L ⊗[K] K
  let M₁ := M ⊗[K] K
  let eL : L₁ ≃ₐ[L] L := Algebra.TensorProduct.rid K L L
  let eM : M₁ ≃ₐ[M] M := Algebra.TensorProduct.rid K M M
  have hL₁ : IsField L₁ := eL.toRingEquiv.isField (Field.toIsField L)
  have hM₁ : IsField M₁ := eM.toRingEquiv.isField (Field.toIsField M)
  refine ⟨hL₁, hM₁, ?_⟩
  let := hL₁.toField
  let := hM₁.toField
  let ι : L₁ →ₐ[K] M₁ :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K K)
  let : Algebra L₁ M₁ := ι.toRingHom.toAlgebra
  have hcomm : (algebraMap L M).comp eL.toRingHom =
      eM.toRingHom.comp (algebraMap L₁ M₁) := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l k =>
      show algebraMap L M (k • l) = k • algebraMap L M l
      exact (IsScalarTower.toAlgHom K L M).toLinearMap.map_smul k l
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hcomm' : (algebraMap L₁ M₁).comp eL.symm.toRingHom =
      eM.symm.toRingHom.comp (algebraMap L M) := by
    ext l
    apply eM.injective
    have h := DFunLike.congr_fun hcomm (eL.symm l)
    simpa using h.symm
  have hfin : Module.Finite L₁ M₁ :=
    Module.Finite.of_equiv_equiv eL.symm.toRingEquiv eM.symm.toRingEquiv hcomm'
  let := hfin
  have hfinL : Module.Finite L L₁ := Module.Finite.equiv eL.symm.toLinearEquiv
  let := hfinL
  let B₁ := integralClosure B L₁
  let eB : B ≃ₐ[B] B₁ := (IsIntegralClosure.equiv B B L (integralClosure B L)).trans
    ((eL.restrictScalars B).symm.mapIntegralClosure)
  have hB₁ : IsDiscreteValuationRing B₁ :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eB
  let := hB₁
  have hfrac : IsFractionRing B₁ L₁ :=
    integralClosure.isFractionRing_of_finite_extension L L₁
  let := hfrac
  refine ⟨hB₁, hfrac, hfin, ?_⟩
  obtain ⟨hdegree, ξ, z, hgen, heval, a, ha, haw⟩ := hlevel
  have hdeg : Module.finrank L₁ M₁ = p :=
    (Algebra.finrank_eq_of_equiv_equiv eL.toRingEquiv eM.toRingEquiv hcomm).trans hdegree
  have hmapB : ∀ b : B, eL (algebraMap B L₁ b) = algebraMap B L b := by
    intro b
    exact (eL.restrictScalars B).commutes b
  let : IsScalarTower L L₁ M₁ := isScalarTower_tensorProduct_map K L M K
  refine ⟨hdeg, eL.symm ξ, eM.symm z, ?_, ?_, algebraMap B B₁ a, ?_, ?_⟩
  · have hgen' : Algebra.adjoin L {eM.symm z} = ⊤ :=
      adjoin_singleton_algEquiv_eq_top (eM.symm.restrictScalars L) z hgen
    apply (Subalgebra.restrictScalars_injective L)
    rw [Algebra.Subalgebra.restrictScalars_adjoin, hgen', Subalgebra.restrictScalars_top]
    simp
  · apply eM.injective
    show eM (Polynomial.eval₂ ((algebraMap L₁ M₁).comp (algebraMap B₁ L₁))
      (eM.symm z) (P.map (algebraMap B B₁))) = eM (algebraMap L₁ M₁ (eL.symm ξ))
    show eM.toRingHom _ = eM.toRingHom _
    rw [Polynomial.eval₂_map, Polynomial.hom_eval₂]
    have hcoeff : eM.toRingHom.comp
        (((algebraMap L₁ M₁).comp (algebraMap B₁ L₁)).comp (algebraMap B B₁)) =
        (algebraMap L M).comp (algebraMap B L) := by
      ext b
      simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B B₁ L₁]
      exact (DFunLike.congr_fun hcomm (algebraMap B L₁ b)).symm.trans
        (congrArg (algebraMap L M) (hmapB b))
    rw [hcoeff]
    show Polynomial.eval₂ ((algebraMap L M).comp (algebraMap B L))
      (eM (eM.symm z)) P = eM (algebraMap L₁ M₁ (eL.symm ξ))
    rw [eM.apply_symm_apply, heval]
    simpa using DFunLike.congr_fun hcomm (eL.symm ξ)
  · have hm := IsLocalRing.map_maximalIdeal_of_surjective eB.toRingHom eB.surjective
    rw [← hm]
    convert Ideal.mem_map_of_mem eB.toRingHom ha using 1
    exact (eB.commutes a).symm
  · apply eL.injective
    show eL (algebraMap B₁ L₁ (algebraMap B B₁ a)) =
      eL (algebraMap B₁ L₁ (wElt ((algebraMap B B₁).comp f)) ^ p * eL.symm ξ)
    rw [wElt_comp, ← IsScalarTower.algebraMap_apply B B₁ L₁,
      ← IsScalarTower.algebraMap_apply B B₁ L₁, map_mul, map_pow,
      eL.apply_symm_apply, hmapB, hmapB]
    exact haw

private lemma exists_totallyRamified_radicalExtension
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
    (n : ℕ) (hn : 2 ≤ n) (π : A) (hπ : Irreducible π) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
      (_ : IsScalarTower A K E) (_ : Module.Finite K E),
      IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K E ∧
        Module.finrank K E = n ∧ ∃ t : E, t ^ n = algebraMap A E π := by
  have hirr := Stacks.KummerExtension.kummerPoly_irreducible K π n (by omega) hπ
  have : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π n)) := ⟨hirr⟩
  have : Algebra.IsSeparable K (Stacks.KummerExtension.K1 K π n) := Algebra.IsSeparable.of_integral
    _ _
  refine ⟨Stacks.KummerExtension.K1 K π n, inferInstance, inferInstance, inferInstance,
    inferInstance,
    inferInstance, Stacks.KummerExtension.isTotallyRamified_K1 K π n hn hπ,
    Stacks.KummerExtension.finrank_K1 K π n hn hπ, Stacks.KummerExtension.piRoot K π n, ?_⟩
  show (AdjoinRoot.root (Stacks.KummerExtension.kummerPoly K π n)) ^ n =
    AdjoinRoot.of (Stacks.KummerExtension.kummerPoly K π n) (algebraMap A K π)
  have h := AdjoinRoot.eval₂_root (Stacks.KummerExtension.kummerPoly K π n)
  simpa only [Stacks.KummerExtension.kummerPoly, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] using h

private lemma isTotallyRamifiedWithRespectTo_self
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K := by
  let S := integralClosure A K
  let e : A ≃ₐ[A] S := IsIntegralClosure.equiv A A K S
  let : IsDiscreteValuationRing S :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  let m := IsLocalRing.maximalIdeal S
  have hm : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
  have hl : m.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) m)).symm⟩
  refine ⟨m, hm, hl, fun n hn _ => IsLocalRing.eq_maximalIdeal hn, ?_⟩
  let := hl
  let := Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal A)
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let : Field (S ⧸ m) := Ideal.Quotient.field _
  let : Module.Free (A ⧸ IsLocalRing.maximalIdeal A) (S ⧸ m) :=
    Module.Free.of_divisionRing _ _
  have hone : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (S ⧸ m) = 1 := by
    apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    refine ⟨(algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (S ⧸ m)).injective, ?_⟩
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := e.surjective x
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    exact (Ideal.Quotient.algebraMap_mk_of_liesOver m
      (IsLocalRing.maximalIdeal A) a).trans
        (congrArg (Ideal.Quotient.mk m) (by simp))
  simpa using hone

private lemma exists_isWeakSolution_of_reduced_tensorProduct
    (A C K M E A₁ R : Type u)
    [CommRing A] [CommRing C] [IsDomain A] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing C]
    [Field K] [Field M] [Field E] [CommRing A₁] [CommRing R]
    [Algebra A C] [Algebra A K] [Algebra C M] [Algebra A M]
    [Algebra K M] [Algebra K E] [Algebra A E]
    [IsFractionRing A K] [IsFractionRing C M] [IsDiscreteValuationRing.IsExtension A C]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower A K E]
    [Module.Finite K E]
    [Algebra A A₁] [Algebra A₁ E] [IsScalarTower A A₁ E]
    [IsIntegralClosure A₁ A E]
    [Algebra C R] [Algebra R (M ⊗[K] E)] [IsScalarTower C R (M ⊗[K] E)]
    [IsIntegralClosure R C (M ⊗[K] E)]
    [Algebra A R] [Algebra A₁ R] [IsScalarTower A C R] [IsScalarTower A A₁ R]
    (hnil : nilradical (M ⊗[K] E) = ⊥)
    (hsquare : ∀ a : A₁,
      algebraMap R (M ⊗[K] E) (algebraMap A₁ R a) =
        (Algebra.TensorProduct.includeRight : E →ₐ[K] M ⊗[K] E) (algebraMap A₁ E a))
    (hweak : ∀ q : Ideal R, q.IsMaximal → q.ramificationIdx A₁ = 1) :
    ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M E,
      D.IsWeakSolution := by
  let T := M ⊗[K] E
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let eQ : T ≃ₐ[K] (T ⧸ nilradical T) :=
    (AlgEquiv.quotientBot K T).symm.trans
      (Ideal.quotientEquivAlg ⊥ (nilradical T) (AlgEquiv.refl : T ≃ₐ[K] T)
        (by simpa using hnil))
  let D : IsDiscreteValuationRing.IntegralClosureBaseChange A C K M E :=
    { L₁ := T
      A₁ := A₁
      B₁ := R
      eL₁ := eQ
      eL₁_left := by
        intro x
        simp only [eQ, Ideal.quotientEquivAlg]
        rfl
      eL₁_right := by
        intro x
        simp only [eQ, Ideal.quotientEquivAlg]
        rfl
      ringSquare := hsquare }
  exact ⟨D, hweak⟩

private lemma exists_isWeakSolution_self_of_isWeaklyUnramified
    (A B K L : Type u)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsDiscreteValuationRing.IsExtension A B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
      A B K L K, D.IsWeakSolution := by
  let T := L ⊗[K] K
  let e : T ≃ₐ[K] L := Algebra.TensorProduct.rid K K L
  have hnil : nilradical T = ⊥ :=
    have := isReduced_of_injective e.toRingHom e.injective
    nilradical_eq_zero T
  let eQ : T ≃ₐ[K] (T ⧸ nilradical T) :=
    (AlgEquiv.quotientBot K T).symm.trans
      (Ideal.quotientEquivAlg ⊥ (nilradical T) (AlgEquiv.refl : T ≃ₐ[K] T)
        (by simpa using hnil))
  let D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K :=
    { L₁ := L
      A₁ := A
      B₁ := B
      eL₁ := e.symm.trans eQ
      eL₁_left := by
        intro x
        show eQ (e.symm x) = _
        simp only [eQ, AlgEquiv.trans_apply, AlgEquiv.quotientBot_symm_mk,
          Ideal.quotientEquivAlg]
        rfl
      eL₁_right := by
        intro x
        show eQ (e.symm (algebraMap K L x)) = _
        have hx : e.symm (algebraMap K L x) = (1 : L) ⊗ₜ[K] x := by
          apply e.injective
          rw [e.apply_symm_apply]
          show (algebraMap K L) x = (Algebra.TensorProduct.rid K K L) (1 ⊗ₜ[K] x)
          simp [Algebra.smul_def]
        rw [hx]
        simp only [eQ, AlgEquiv.trans_apply, AlgEquiv.quotientBot_symm_mk,
          Ideal.quotientEquivAlg]
        rfl
      ringSquare := by
        intro a
        exact (IsScalarTower.algebraMap_apply A B L a).symm.trans
          (IsScalarTower.algebraMap_apply A K L a) }
  refine ⟨D, ?_⟩
  intro q hq
  show q.ramificationIdx A = 1
  rw [IsLocalRing.eq_maximalIdeal hq]
  exact (IsDiscreteValuationRing.isWeaklyUnramified_iff_ramificationIdx_eq_one A B).mp hweak

/-- In mixed characteristic, a weakly unramified tower followed by a Galois extension of
prime degree admits a finite, totally ramified base extension. This base extension
is either a weak solution for the full tower or makes the canonical tensor-product
extension a degree-`p` extension of finite level. -/
@[stacks 09F4]
theorem exists_totallyRamified_galoisExtension_isWeakSolution_or_finiteLevel
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower A B L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K L]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) [Fact p.Prime] [CharZero K]
    [CharP (IsLocalRing.ResidueField A) p]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (f : CyclotomicRing p ℤ ℚ →+* B)
    [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁ ∧
        ((∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M
          K₁,
            D.IsWeakSolution) ∨
          let L₁ := L ⊗[K] K₁
          let M₁ := M ⊗[K] K₁
          ∃ (hL₁ : IsField L₁) (hM₁ : IsField M₁),
            letI := hL₁.toField
            letI := hM₁.toField
            let ι : L₁ →ₐ[K] M₁ :=
              Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K K₁)
            letI : Algebra L₁ M₁ := ι.toRingHom.toAlgebra
            let B₁ := integralClosure B L₁
            ∃ (hB₁ : IsDiscreteValuationRing B₁) (hfrac : IsFractionRing B₁ L₁)
              (hfin : Module.Finite L₁ M₁),
              letI := hB₁
              letI := hfrac
              letI := hfin
              ∃ P : Polynomial B,
                intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P ∧
                  IsDegreePExtensionOfFiniteLevel B₁ L₁ M₁ p
                    ((algebraMap B B₁).comp f) (P.map (algebraMap B B₁))) := by
  by_cases hAC : IsDiscreteValuationRing.IsWeaklyUnramified A C
  · refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, isTotallyRamifiedWithRespectTo_self A K, Or.inl ?_⟩
    exact exists_isWeakSolution_self_of_isWeaklyUnramified A C K M hAC
  · have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    obtain ⟨y, b, hy, hgen⟩ := exists_pow_eq_and_adjoin_eq_top_of_prime_degree
      p ((algebraMap B L).comp f) hdegree
    have hb := kummer_parameter_ne_zero p (Fact.out : p.Prime).one_lt
      y b hy hgen hdegree
    obtain ⟨πA, hπA⟩ := IsDiscreteValuationRing.exists_irreducible A
    let π := algebraMap A B πA
    have hπ : Irreducible π :=
      (isWeaklyUnramified_iff_irreducible_algebraMap A B πA hπA).mp hweak
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hb
    have hunitpow : y ^ p = algebraMap L M
        (algebraMap B L (u : B) * algebraMap B L π ^ n) := by
      simpa only [hu, Units.smul_def, Algebra.smul_def] using hy
    by_cases hn : (p : ℤ) ∣ n
    · obtain ⟨z, hz, hzg⟩ := exists_pow_eq_unit_of_pow_eq_unit_mul_zpow p y u
        (algebraMap B L π)
        ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hπ.ne_zero)
        n hunitpow hn
      have hzgen : Algebra.adjoin L {z} = ⊤ := hzg.trans hgen
      have : CharZero B := (RingHom.charZero_iff (IsFractionRing.injective B L)).mpr inferInstance
      obtain ⟨P, hP, hquot, hshape, hfunc⟩ :=
        main_statement f
      have hzB : z ^ p = algebraMap B M (u : B) := by
        rw [IsScalarTower.algebraMap_apply B L M]
        exact hz
      rcases isWeaklyUnramified_or_finiteLevel_of_pow_eq_unit B C L M p f P hP
          hdegree z hzgen u hzB with hBC | hlevel
      · exact (hAC (IsDiscreteValuationRing.isWeaklyUnramified_trans A B C hweak hBC)).elim
      · obtain ⟨hL₁, hM₁, hB₁, hfrac, hfin, hlevel₁⟩ :=
          finiteLevel_tensorProduct_self B K L M p f P hlevel
        refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
          inferInstance, isTotallyRamifiedWithRespectTo_self A K, Or.inr ?_⟩
        exact ⟨hL₁, hM₁, hB₁, hfrac, hfin, P, hP, hquot, hshape, hfunc, hlevel₁⟩
    · let : IsDiscreteValuationRing (integralClosure B M) :=
        isDiscreteValuationRing_integralClosure_of_pow_eq_unit_mul_zpow B L M
          p hdegree π hπ u n y hunitpow hn
      obtain ⟨eC⟩ := integralClosure_algEquiv_of_isDiscreteValuationRing B C L M
      let : Algebra.IsIntegral B C := Algebra.IsIntegral.of_surjective eC.toAlgHom eC.surjective
      · obtain ⟨E, hE, hKE, hAE, hAKE, hfinE, htot, hdegE, t, ht⟩ :=
          exists_totallyRamified_radicalExtension A K p
            (Fact.out : p.Prime).two_le πA hπA
        let := hE
        let := hKE
        let := hAE
        let := hAKE
        let := hfinE
        have hweakIdeal : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
            IsLocalRing.maximalIdeal B := by
          have h := (IsDiscreteValuationRing.ramificationIndex_characterization A B).2.1
          change IsDiscreteValuationRing.ramificationIndex A B = 1 at hweak
          simpa only [hweak, pow_one] using h
        obtain ⟨hL₁, hA₁, hBdom, hBdvr, hinj, hweakT, hCdom, hB₁, hfrac,
            eB, heB, hinjB, hweakB⟩ :=
          IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified
            A B K L E hweakIdeal htot
        let := hL₁.toField
        let L₁ := L ⊗[K] E
        let M₁ := M ⊗[K] E
        let B₁ := integralClosure B L₁
        let := hB₁
        let := hfrac
        by_cases hM₁ : IsField M₁
        · let := hM₁.toField
          let ι := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K E)
          let : Algebra L₁ M₁ := ι.toRingHom.toAlgebra
          obtain ⟨hfin, hdeg⟩ := finite_finrank_tensorProduct_map K L M E hL₁
          let := hfin
          have hparam : y ^ p = algebraMap L M
              (algebraMap B L u * algebraMap K L (algebraMap A K πA) ^ n) := by
            simpa only [π, ← IsScalarTower.algebraMap_apply A B L,
              ← IsScalarTower.algebraMap_apply A K L] using hunitpow
          have htK : t ^ p = algebraMap K E (algebraMap A K πA) := by
            rwa [← IsScalarTower.algebraMap_apply A K E]
          obtain ⟨z, hz, hzgen⟩ := exists_pow_eq_unit_tensorProduct_of_pow_eq B K L M E
            p (Fact.out : p.Prime).ne_zero (algebraMap A K πA)
            ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hπA.ne_zero)
            y u n hparam hgen t htK hL₁ hM₁
          let u₁ : B₁ˣ := Units.map (algebraMap B B₁).toMonoidHom u
          have hz₁ : z ^ p = algebraMap L₁ M₁ (algebraMap B₁ L₁ u₁) := by
            show z ^ p = algebraMap L₁ M₁
              (algebraMap B₁ L₁ (algebraMap B B₁ (u : B)))
            rw [← IsScalarTower.algebraMap_apply B B₁ L₁]
            exact hz
          by_cases hres : ∃ r : IsLocalRing.ResidueField B₁,
              IsLocalRing.residue B₁ u₁ = r ^ p
          · have : CharZero L₁ := charZero_of_injective_algebraMap (algebraMap L L₁).injective
            have : CharZero B₁ :=
              (RingHom.charZero_iff (IsFractionRing.injective B₁ L₁)).mpr inferInstance
            obtain ⟨P, hP, hquot, hshape, hfunc⟩ :=
              main_statement f
            have hlevel := isDegreePExtensionOfFiniteLevel_of_pow_eq_unit p
              ((algebraMap B B₁).comp f) (P.map (algebraMap B B₁))
              (intProp_map f (algebraMap B B₁) P hP) (hdeg.trans hdegree)
              z hzgen u₁ hz₁ hres
            exact ⟨E, hE, hKE, hAE, hAKE, hfinE, htot,
              Or.inr ⟨hL₁, hM₁, hB₁, hfrac, hfin, P, hP, hquot, hshape, hfunc, hlevel⟩⟩
          · let : IsScalarTower L L₁ M₁ := isScalarTower_tensorProduct_map K L M E
            let : Algebra B₁ M₁ :=
              ((algebraMap L₁ M₁).comp (algebraMap B₁ L₁)).toAlgebra
            let : IsScalarTower B₁ L₁ M₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
            let : IsScalarTower B L₁ M₁ := IsScalarTower.of_algebraMap_eq fun b => by
              show algebraMap B M b ⊗ₜ[K] (1 : E) =
                ι (algebraMap B L b ⊗ₜ[K] 1)
              simp [ι, ← IsScalarTower.algebraMap_apply B L M]
            let : IsScalarTower B B₁ M₁ := IsScalarTower.of_algebraMap_eq fun b => by
              rw [IsScalarTower.algebraMap_apply B L₁ M₁,
                IsScalarTower.algebraMap_apply B B₁ L₁]
              rfl
            have hzS : z ^ p = algebraMap B₁ M₁ (u₁ : B₁) := hz₁
            obtain ⟨hS, hπS⟩ :=
              isDiscreteValuationRing_integralClosure_and_irreducible_of_pow_eq
                (K := L₁) p (u₁ : B₁) hres z hzS hzgen
            let S := integralClosure B₁ M₁
            let R := integralClosure C M₁
            let : IsDiscreteValuationRing S := hS
            obtain ⟨e, heval⟩ := exists_integralClosure_algEquiv_of_isIntegral B B₁ C M₁
            have hweakS :=
              Stacks.DiscreteValuationRing.AdjoinPthRoot.maximalIdeal_map_eq_of_pow_eq (K := L₁) p
                (u₁ : B₁) hres z hzS hzgen
            let A₁ := integralClosure A E
            let := hA₁
            have hweakIdx :=
              @Stacks.DiscreteValuationRing.WeakUnramifiedTransfer.weak_indices_through_equivalence
                A₁ B₁ S R
                inferInstance inferInstance inferInstance inferInstance
                hA₁.toIsLocalRing hB₁.toIsLocalRing hS.toIsLocalRing
                (eB.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
                (algebraMap B₁ S) e.toRingEquiv hweakB hweakS
            let g : A₁ →+* R := e.toRingHom.comp
              ((algebraMap B₁ S).comp
                (eB.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))
            let : Algebra A₁ R := g.toAlgebra
            have hg : ∀ a : A₁, algebraMap R M₁ (g a) =
                (Algebra.TensorProduct.includeRight : E →ₐ[K] M₁) (a : E) := by
              intro a
              show (e ((algebraMap B₁ S)
                (eB ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a))) : M₁) = _
              rw [heval]
              show algebraMap B₁ M₁
                (eB ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a)) = _
              rw [IsScalarTower.algebraMap_apply B₁ L₁ M₁]
              show ι ((eB ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a) : B₁) :
                L₁) = _
              rw [heB]
              simp [ι]
            let : IsScalarTower A A₁ R :=
              Stacks.DiscreteValuationRing.WeakUnramifiedTransfer.scalarTower_of_injective_square A
                A₁ R E M₁
                ((Algebra.TensorProduct.includeRight : E →ₐ[K] M₁).restrictScalars A) g
                (IsIntegralClosure.algebraMap_injective R C M₁) hg
            have hnil : nilradical M₁ = ⊥ := nilradical_eq_zero M₁
            have hsolution := exists_isWeakSolution_of_reduced_tensorProduct A C K M E A₁ R
              hnil hg hweakIdx
            exact ⟨E, hE, hKE, hAE, hAKE, hfinE, htot, Or.inl hsolution⟩
        · let := hA₁
          have hsolution :=
            Stacks.WeakSolution.NonfieldKummer.exists_weakSolution_of_nondivisible_kummer_nonfield
              A B C K L M E hweak p (Fact.out : p.Prime) hdegree hdegE
              π hπ u n y hunitpow hn hgen htot hL₁ hM₁
          exact ⟨E, hE, hKE, hAE, hAKE, hfinE, htot, Or.inl hsolution⟩

end Stacks.DegreePExtensionLevel
