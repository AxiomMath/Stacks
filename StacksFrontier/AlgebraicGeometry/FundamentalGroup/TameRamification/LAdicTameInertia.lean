module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.LAdicTameCharacter
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.SeparableClosureInertia
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Invariant.Profinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `ℓ`-adic tame character of a discretely valued field with finite residue field

Let `A` be a discrete valuation ring with fraction field `K` and finite residue field of
cardinality `q` and characteristic `p`, let `L` be a separable closure of `K`, `P` a maximal ideal
of the integral closure `B` of `A` in `L`, `D ⊆ Gal(L/K)` its decomposition group and `I ⊆ D` its
inertia group.  For a prime `ℓ ≠ p` this file constructs the `ℓ`-adic tame character
`t : I → ℤ_ℓ`, the input of Grothendieck's local monodromy theorem, with its three properties:

* `t` is continuous;
* its kernel is pro-prime-to-`ℓ`: every open subgroup of `Gal(L/K)` contains a power `σ ^ m`,
  `m` prime to `ℓ`, of every `σ ∈ ker t`;
* an arithmetic Frobenius `Fr ∈ D` (acting on `B / P` by `x ↦ x ^ q`) acts on tame inertia by
  the `q`-th power: `Fr σ Fr⁻¹ σ⁻ᵠ` lies in `ker t`, and is even pro-`p`;

and the existence of arithmetic Frobenius elements.  The character is
`Stacks.FundamentalGroup.ladicCharacter` of the `ℓ ^ k`-components of the tame inertia character
`Stacks.FundamentalGroup.exists_primeToChar_tameInertiaCharacter`, read against a compatible
system of primitive `ℓ ^ k`-th roots of unity in the algebraically closed residue field `B / P`.

## Main results

* `Stacks.FundamentalGroup.exists_ladicTameCharacter`: the `ℓ`-adic tame character and its
  properties.
* `Stacks.FundamentalGroup.exists_mem_stabilizer_smul_sub_pow_mem`: arithmetic Frobenius
  elements exist.
* `Stacks.FundamentalGroup.exists_tameInertiaCharacter_finiteLevel`: local constancy of the tame
  inertia character, and the finite-level order bound behind both properties of its kernel.
* `Stacks.FundamentalGroup.exists_pow_mul_pow_eq_one_of_canonicalInertiaCharacter_eq_one`: in a
  finite Galois extension, the kernel of the canonical tame character consists of `p`-elements.

## References

* A. Grothendieck, appendix to J.-P. Serre and J. Tate, *Good reduction of abelian varieties*,
  Ann. of Math. 88 (1968).
* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.7.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open scoped Pointwise

universe u v w

namespace Stacks.FundamentalGroup

/-- **Elements of a finite inertia group with trivial tame character are `p`-elements.**  In a
finite Galois extension `F / K` of the fraction field of a discrete valuation ring with residue
characteristic `p > 0`, if the canonical tame inertia character kills `σ ^ m`, then
`σ ^ (m * p ^ c) = 1` for some `c`: the kernel of the canonical character is the wild inertia
group, a `p`-group. -/
@[sga "1 XIII 2.0" "special case"]
public theorem exists_pow_mul_pow_eq_one_of_canonicalInertiaCharacter_eq_one
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (F : Type*) [Field F] [Algebra K F] [FiniteDimensional K F]
    [IsGalois K F] [Algebra A F] [IsScalarTower A K F]
    (qF : Ideal (integralClosure A F)) [qF.IsMaximal]
    (hp : 0 < ringChar (IsLocalRing.ResidueField A)) :
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    ∀ (σ : qF.inertia Gal(F/K)) (m : ℕ),
      IsDiscreteValuationRing.canonicalInertiaCharacter A K F qF (σ ^ m) = 1 →
      ∃ c : ℕ, σ ^ (m * ringChar (IsLocalRing.ResidueField A) ^ c) = 1 := by
  let := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  intro σ m h1
  have h2 : IsDiscreteValuationRing.inertiaCharacter A K F qF
      (σ ^ (m * IsDiscreteValuationRing.wildRamificationFactor A F qF)) = 1 := by
    have := congrArg (fun x : rootsOfUnity (IsDiscreteValuationRing.tameRamificationIndex A F qF)
      (integralClosure A F ⧸ qF) => (x : (integralClosure A F ⧸ qF)ˣ)) h1
    simp only [IsDiscreteValuationRing.canonicalInertiaCharacter_coe, OneMemClass.coe_one] at this
    refine Subtype.ext ?_
    rw [pow_mul, map_pow, SubmonoidClass.coe_pow, this, OneMemClass.coe_one]
  obtain ⟨W, -, -, -, -, hpg, -, -, θ', -, hexact, -, -, -, hchar, -⟩ :=
    IsDiscreteValuationRing.exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity A K F qF
  have hmem : σ ^ (m * IsDiscreteValuationRing.wildRamificationFactor A F qF) ∈
      W.subtype.range := by
    rwa [← hexact.monoidHom_ker_eq, MonoidHom.mem_ker,
      IsDiscreteValuationRing.inertiaCharacter_eq A K F qF θ' hchar]
  obtain ⟨x, hx⟩ := hmem
  obtain ⟨c, hc⟩ := hpg hp x
  refine ⟨(qF.ramificationIdx A).factorization (ringChar (IsLocalRing.ResidueField A)) + c, ?_⟩
  rw [pow_add, ← mul_assoc, pow_mul, ← hx, ← map_pow, hc, map_one]

/-- **Arithmetic Frobenius elements exist.**  For a discrete valuation ring `A` with finite
residue field of cardinality `q`, a separable closure `L` of its fraction field `K` and a maximal
ideal `P` of the integral closure `B` of `A` in `L`, some element of the decomposition group of
`P` acts on `B / P` by `x ↦ x ^ q`: the decomposition group surjects onto the automorphisms of
`B / P` over the residue field of `A`. -/
public theorem exists_mem_stabilizer_smul_sub_pow_mem
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] [Finite (IsLocalRing.ResidueField A)] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∃ Fr ∈ MulAction.stabilizer Gal(L/K) P, ∀ b : integralClosure A L,
      Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  have : IsGalois K L := inferInstance
  have : Algebra.IsIntegral K L := inferInstance
  let : TopologicalSpace (integralClosure A L) := ⊥
  have : DiscreteTopology (integralClosure A L) := ⟨rfl⟩
  have hinj := FaithfulSMul.algebraMap_injective (integralClosure A L) L
  have hgal : ∀ (σ : Gal(L/K)) (b : integralClosure A L),
      algebraMap (integralClosure A L) L (σ • b) = σ (algebraMap (integralClosure A L) L b) :=
    algebraMap_galRestrict_apply A
  have : ContinuousSMul Gal(L/K) (integralClosure A L) :=
    continuousSMul_iff_stabilizer_isOpen.mpr (fun b ↦ by
      have h : (MulAction.stabilizer Gal(L/K) b : Set Gal(L/K)) =
          MulAction.stabilizer Gal(L/K) (algebraMap (integralClosure A L) L b) := by
        ext σ
        simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        rw [← hinj.eq_iff, hgal]
      rw [h]
      exact stabilizer_isOpen_of_isIntegral (algebraMap (integralClosure A L) L b))
  have : Algebra.IsInvariant A (integralClosure A L) Gal(L/K) := by
    refine ⟨fun b hb ↦ ?_⟩
    have hb' : algebraMap (integralClosure A L) L b ∈
        IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by
      rintro ⟨σ, -⟩
      exact (hgal σ b).symm.trans (congrArg (algebraMap (integralClosure A L) L) (hb σ))
    rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hb'
    obtain ⟨k, hk⟩ := hb'
    have hbint : IsIntegral A b := IsIntegralClosure.isIntegral A L b
    rw [← isIntegral_algebraMap_iff (B := L), ← hk, isIntegral_algebraMap_iff] at hbint
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hbint
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A
      (integralClosure A L) L, hinj.eq_iff] at hk
    exact ⟨a, hk⟩
  let : SMulCommClass Gal(L/K) A (integralClosure A L) :=
    ⟨fun g a b ↦ by
      simp only [Algebra.smul_def]
      show galRestrict A K L (integralClosure A L) g (algebraMap A _ a * b) =
        algebraMap A _ a * galRestrict A K L (integralClosure A L) g b
      rw [map_mul, AlgEquiv.commutes]⟩
  have hPA : P.under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)
  have : P.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hPA.symm⟩
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  let : Field (integralClosure A L ⧸ P) := Ideal.Quotient.field P
  let : Fintype (A ⧸ IsLocalRing.maximalIdeal A) :=
    Fintype.ofFinite (IsLocalRing.ResidueField A)
  have : Algebra.IsIntegral A (integralClosure A L) := inferInstance
  have : Algebra.IsAlgebraic (A ⧸ IsLocalRing.maximalIdeal A) (integralClosure A L ⧸ P) :=
    Algebra.IsIntegral.isAlgebraic
  obtain ⟨⟨Fr, hFrD⟩, hFr⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Gal(L/K)) (IsLocalRing.maximalIdeal A) P
    (FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ IsLocalRing.maximalIdeal A)
      (integralClosure A L ⧸ P))
  refine ⟨Fr, hFrD, fun b => Ideal.Quotient.eq.1 ?_⟩
  have h := DFunLike.congr_fun hFr (Ideal.Quotient.mk P b)
  rw [Ideal.Quotient.stabilizerHom_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic] at h
  have hq : Nat.card (IsLocalRing.ResidueField A) =
      Fintype.card (A ⧸ IsLocalRing.maximalIdeal A) :=
    Nat.card_eq_fintype_card (α := A ⧸ IsLocalRing.maximalIdeal A)
  rwa [map_pow, hq]

/-- **The tame inertia character at finite levels** (an auxiliary form of
`Stacks.FundamentalGroup.exists_primeToChar_tameInertiaCharacter` for residue characteristic
`p > 0`).  The tame inertia character `θ` of a separable closure has components which are
locally constant (each is trivial on an open subgroup), and if the components of `θ σ` of order
dividing `n`, for `n` dividing the tame ramification index `e` of a finite level, vanish, then
modulo any given open subgroup `σ` has order dividing `(e / n) p ^ c`. -/
public theorem exists_tameInertiaCharacter_finiteLevel
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (hp : (ringChar (IsLocalRing.ResidueField A)).Prime) :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    let I := P.inertia Gal(L/K)
    let D := MulAction.stabilizer Gal(L/K) P
    let p := ringChar (IsLocalRing.ResidueField A)
    let N := {n : ℕ // 0 < n ∧ (p = 0 ∨ Nat.Coprime n p)}
    ∃ θ : I →* (∀ _ : N, (B ⧸ P)ˣ),
      (∀ σ : I, ∀ n : N, (θ σ n) ^ n.1 = 1) ∧
      (∀ σ : I, ∀ n m : N, n.1 ∣ m.1 → (θ σ m) ^ (m.1 / n.1) = θ σ n) ∧
      (∀ τ : D, ∀ σ : I, ∃ ρ : I,
          (ρ : Gal(L/K)) = (τ : Gal(L/K)) * (σ : Gal(L/K)) * (τ : Gal(L/K))⁻¹ ∧
          ∀ n : N, θ ρ n =
            (Ideal.quotientEquiv P P
              ((MulSemiringAction.toRingEquiv Gal(L/K) B) (τ : Gal(L/K)))
              τ.property.symm).toMulEquiv (θ σ n)) ∧
      (∀ n : N, ∃ U : OpenSubgroup Gal(L/K), ∀ σ : I, (σ : Gal(L/K)) ∈ U → θ σ n = 1) ∧
      (∀ (σ : I) (U : OpenSubgroup Gal(L/K)), ∃ e : ℕ, 0 < e ∧ e.Coprime p ∧
        ∀ n : N, n.1 ∣ e → θ σ n = 1 → ∃ c : ℕ, (σ : Gal(L/K)) ^ (e / n.1 * p ^ c) ∈ U) := by
  classical
  intro B I D p N
  let : MulSemiringAction Gal(L/K) B := IsIntegralClosure.MulSemiringAction A K L B
  obtain ⟨θ, horder, hcompat, -, hconj, -, hfinite, -, -⟩ :=
    exists_primeToChar_tameInertiaCharacter.{u, v, w, 0} A K L P
  obtain ⟨S, -, hSpos, hScop, -, -, -, θS, -, -, -, -, -, hSfin, -⟩ :=
    exists_tameInertiaCharacter.{u, v, w, 0} A K L P
  -- restriction to a finite Galois subextension fixed by `σ` is trivial
  have hres : ∀ (F : FiniteGaloisIntermediateField K L) (σ : Gal(L/K)),
      σ ∈ (F : IntermediateField K L).fixingSubgroup →
        AlgEquiv.restrictNormal σ (F : IntermediateField K L) = 1 := fun F σ hσ =>
    AlgEquiv.ext fun x => Subtype.ext ((AlgEquiv.restrictNormal_commutes σ _ x).trans
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ x.2))
  -- local constancy of the components of the tame character
  have hLC : ∀ n : N, ∃ F : FiniteGaloisIntermediateField K L, ∀ σ : I,
      (σ : Gal(L/K)) ∈ (F : IntermediateField K L).fixingSubgroup → θ σ n = 1 := by
    intro n
    obtain ⟨F, hq, hdiv⟩ := primeToChar_divides_tameRamificationIndex A K L P n.1 n.2.1 n.2.2
    refine ⟨F, fun σ hσ => ?_⟩
    let C := integralClosure A F
    let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let f : C →ₐ[A] integralClosure A L := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
    let qF := P.comap f.toRingHom
    let : qF.IsMaximal := hq
    obtain ⟨σF, hσF, hval⟩ := hfinite F n hdiv σ
    have h1 : σF = 1 := Subtype.ext (hσF.trans (hres F σ hσ))
    rw [h1, map_one] at hval
    refine Units.ext (hval.trans ?_)
    rw [OneMemClass.coe_one, Units.val_one, one_pow, map_one, Units.val_one]
  -- the key finite-level computation: an element of inertia on which the components of the
  -- tame character of order dividing the tame ramification index `e` of a finite level vanish
  -- has, modulo the open subgroup, order dividing `e / n` times a power of `p`
  have hKey : ∀ (σ : I) (U : OpenSubgroup Gal(L/K)), ∃ e : ℕ, 0 < e ∧ e.Coprime p ∧
      ∀ n : N, n.1 ∣ e → θ σ n = 1 → ∃ c : ℕ, (σ : Gal(L/K)) ^ (e / n.1 * p ^ c) ∈ U := by
    intro σ U
    obtain ⟨E, hEfin, hEnorm, hEU⟩ :=
      (krullTopology_mem_nhds_one_iff_of_normal K L _).1 (U.isOpen.mem_nhds U.one_mem)
    let : FiniteDimensional K E := hEfin
    let : IsGalois K E := isGalois_iff.mpr ⟨inferInstance, hEnorm⟩
    let F : FiniteGaloisIntermediateField K L := ⟨E⟩
    let C := integralClosure A F
    let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let f : C →ₐ[A] integralClosure A L := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
    let qF := P.comap f.toRingHom
    have hq : qF.IsMaximal := by
      let : Algebra C (integralClosure A L) := f.toRingHom.toAlgebra
      let : IsScalarTower A C (integralClosure A L) :=
        IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
      let : Algebra.IsIntegral C (integralClosure A L) := Algebra.IsIntegral.tower_top A
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    let : qF.IsMaximal := hq
    let : MulSemiringAction Gal(F/K) C := IsIntegralClosure.MulSemiringAction A K F C
    obtain ⟨heS, -⟩ := hSfin F
    refine ⟨_, hSpos _ heS, hScop hp.ne_zero _ heS, fun n hn hθ => ?_⟩
    obtain ⟨σF, hσF, hval⟩ := hfinite F n hn σ
    let : Field (C ⧸ qF) := Ideal.Quotient.field qF
    have h1 : IsDiscreteValuationRing.canonicalInertiaCharacter A K F qF
        (σF ^ (IsDiscreteValuationRing.tameRamificationIndex A F qF / n.1)) = 1 := by
      refine Subtype.ext (Units.ext ((Ideal.quotientMap P f.toRingHom le_rfl).injective ?_))
      rw [map_pow]
      simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one, map_one]
      rw [← hval, hθ, Units.val_one]
    obtain ⟨c, hc⟩ := exists_pow_mul_pow_eq_one_of_canonicalInertiaCharacter_eq_one A K F qF
      hp.pos σF _ h1
    refine ⟨c, hEU ?_⟩
    have : Normal K E := hEnorm
    have hker : (σ : Gal(L/K)) ^ (IsDiscreteValuationRing.tameRamificationIndex A F qF / n.1 *
        p ^ c) ∈ (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      show (AlgEquiv.restrictNormal (σ : Gal(L/K)) (F : IntermediateField K L)) ^ _ = 1
      rw [← hσF, ← Subgroup.coe_pow, hc, Subgroup.coe_one]
    rwa [IntermediateField.restrictNormalHom_ker E] at hker
  refine ⟨θ, horder, hcompat, hconj, fun n => ?_, hKey⟩
  obtain ⟨F, hF⟩ := hLC n
  exact ⟨⟨(F : IntermediateField K L).fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen _⟩, hF⟩

/-- **The `ℓ`-adic tame character** (Grothendieck; Weil II 1.7).  For a discrete valuation ring
`A` with finite residue field of characteristic `p` and cardinality `q`, a separable closure `L`
of its fraction field `K`, a maximal ideal `P` of the integral closure `B` of `A` in `L`, with
inertia group `I` and decomposition group `D`, and a prime `ℓ ≠ p`, there is a continuous
homomorphism `t : I → ℤ_ℓ` such that

1. every element of `ker t` is pro-prime-to-`ℓ`: each open subgroup of `Gal(L/K)` contains one of
   its powers with exponent prime to `ℓ`;
2. for every arithmetic Frobenius `Fr ∈ D`, i.e. acting on `B / P` by `x ↦ x ^ q`, and `σ ∈ I`,
   `τ = Fr σ Fr⁻¹ σ⁻ᵠ` lies in `I ∩ ker t`, and is pro-`p`: each open subgroup of `Gal(L/K)`
   contains some `τ ^ (p ^ k)`;
3. arithmetic Frobenius elements exist. -/
@[sga "7 I 0.3" "special case"]
public theorem exists_ladicTameCharacter
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [Finite (IsLocalRing.ResidueField A)] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ ringChar (IsLocalRing.ResidueField A)) :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    let I := P.inertia Gal(L/K)
    let D := MulAction.stabilizer Gal(L/K) P
    let p := ringChar (IsLocalRing.ResidueField A)
    let q := Nat.card (IsLocalRing.ResidueField A)
    ∃ t : I →* Multiplicative ℤ_[ℓ], Continuous t ∧
      (∀ σ : I, t σ = 1 → ∀ U : OpenSubgroup Gal(L/K),
        ∃ m : ℕ, ℓ.Coprime m ∧ (σ : Gal(L/K)) ^ m ∈ U) ∧
      (∀ Fr ∈ D, (∀ b : B, Fr • b - b ^ q ∈ P) → ∀ σ : I,
        ∃ τ : I, (τ : Gal(L/K)) = Fr * σ * Fr⁻¹ * ((σ : Gal(L/K)) ^ q)⁻¹ ∧ t τ = 1 ∧
          ∀ U : OpenSubgroup Gal(L/K), ∃ k : ℕ, (τ : Gal(L/K)) ^ (p ^ k) ∈ U) ∧
      (∃ Fr ∈ D, ∀ b : B, Fr • b - b ^ q ∈ P) := by
  classical
  intro B I D p q
  let : MulSemiringAction Gal(L/K) B := IsIntegralClosure.MulSemiringAction A K L B
  let N := {n : ℕ // 0 < n ∧ (p = 0 ∨ Nat.Coprime n p)}
  have hp : p.Prime := CharP.char_is_prime (IsLocalRing.ResidueField A) p
  obtain ⟨θ, horder, hcompat, hconj, hLC, hKey⟩ :=
    exists_tameInertiaCharacter_finiteLevel A K L P hp
  have hℓp : ℓ.Coprime p := (Nat.coprime_primes (Fact.out) hp).2 hℓ
  let : Field (B ⧸ P) := Ideal.Quotient.field P
  have : IsAlgClosed (B ⧸ P) := isAlgClosed_quotient_integralClosure A K L P
  have hℓA : IsUnit (ℓ : A) :=
    Stacks.KummerExtension.isUnit_natCast_of_coprime_ringChar ℓ (Fact.out : ℓ.Prime).ne_zero
      (Or.inr hℓp.symm)
  have hℓκ : (ℓ : B ⧸ P) ≠ 0 := by
    have := hℓA.map (algebraMap A (B ⧸ P))
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨ζ, hζ, hζc⟩ := exists_compatible_isPrimitiveRoot hℓκ
  let nk : ℕ → N := fun k => ⟨ℓ ^ k, pow_pos (Fact.out : ℓ.Prime).pos k, Or.inr (hℓp.pow_left k)⟩
  let u : I →* (ℕ → (B ⧸ P)ˣ) := Pi.monoidHom fun k => (Pi.evalMonoidHom _ (nk k)).comp θ
  have hu : ∀ σ k, u σ k ^ (ℓ ^ k) = 1 := fun σ k => horder σ (nk k)
  have huc : ∀ σ k, u σ (k + 1) ^ ℓ = u σ k := fun σ k => by
    have h := hcompat σ (nk k) (nk (k + 1)) (pow_dvd_pow ℓ k.le_succ)
    rwa [show (nk (k + 1)).1 / (nk k).1 = ℓ by
      simp only [nk, pow_succ, Nat.mul_div_cancel_left _ (pow_pos (Fact.out : ℓ.Prime).pos k)]] at h
  let t : I →* Multiplicative ℤ_[ℓ] := ladicCharacter hζ hζc u hu huc
  have ht1 : ∀ σ : I, t σ = 1 ↔ ∀ k, θ σ (nk k) = 1 :=
    ladicCharacter_eq_one_iff hζ hζc u hu huc
  have hcont : Continuous t := by
    refine continuous_of_isOpen_toZModPow t fun k => ?_
    have hset : {σ : I | PadicInt.toZModPow k (Multiplicative.toAdd (t σ)) = 0} =
        ((Pi.evalMonoidHom _ (nk k)).comp θ).ker := by
      ext σ
      show _ ↔ θ σ (nk k) = 1
      have := ladicCharacter_spec hζ hζc u hu huc σ k
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [h, ZMod.val_zero, pow_zero] at this
        exact this.symm
      · have hnz : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
        refine ZMod.val_injective _ ((hζ k).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ?_)
        rwa [this, ZMod.val_zero, pow_zero]
    rw [hset]
    obtain ⟨U, hF⟩ := hLC (nk k)
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have hopen : IsOpen ((↑) ⁻¹' (U : Set Gal(L/K)) : Set I) :=
      U.isOpen.preimage continuous_subtype_val
    filter_upwards [hopen.mem_nhds (by simp [one_mem])] with σ hσ
    exact hF σ hσ
  refine ⟨t, hcont, fun σ hσ U => ?_, fun Fr hFrD hFr σ => ?_, ?_⟩
  · -- the kernel of `t` is pro-prime-to-`ℓ`
    obtain ⟨e, he0, -, hK⟩ := hKey σ U
    obtain ⟨c, hc⟩ := hK (nk (e.factorization ℓ)) (Nat.ordProj_dvd e ℓ) ((ht1 σ).1 hσ _)
    exact ⟨_, (Nat.coprime_ordCompl (Fact.out) he0.ne').mul_right (hℓp.pow_right c), hc⟩
  · -- Frobenius acts on tame inertia by the `q`-th power
    obtain ⟨ρ, hρ, hρθ⟩ := hconj ⟨Fr, hFrD⟩ σ
    have hFrP : Fr • P = P := hFrD
    have hpow : ∀ x : B ⧸ P, (Ideal.quotientEquiv P P
        ((MulSemiringAction.toRingEquiv Gal(L/K) B) Fr) hFrP.symm) x = x ^ q := by
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      show Ideal.Quotient.mk P (Fr • b) = _
      rw [← map_pow]
      exact Ideal.Quotient.eq.2 (hFr b)
    obtain ⟨τ, hτ⟩ : ∃ τ : I, τ = ρ * (σ ^ q)⁻¹ := ⟨_, rfl⟩
    have hθτ : θ τ = 1 := by
      funext n
      rw [hτ, map_mul, map_inv, map_pow, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Pi.one_apply,
        mul_inv_eq_one]
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, ← hpow]
      exact hρθ n
    refine ⟨τ, ?_, (ht1 τ).2 fun k => congrFun hθτ (nk k), fun U => ?_⟩
    · rw [hτ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hρ]
    · obtain ⟨e, he0, hecop, hK⟩ := hKey τ U
      obtain ⟨n₀, hn₀⟩ : ∃ n₀ : N, n₀.1 = e := ⟨⟨e, he0, Or.inr hecop⟩, rfl⟩
      obtain ⟨c, hc⟩ := hK n₀ (hn₀ ▸ dvd_refl _) (congrFun hθτ n₀)
      exact ⟨c, by rwa [hn₀, Nat.div_self he0, one_mul] at hc⟩
  · exact exists_mem_stabilizer_smul_sub_pow_mem A K L P

end Stacks.FundamentalGroup
