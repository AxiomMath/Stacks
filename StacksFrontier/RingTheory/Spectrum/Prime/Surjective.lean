module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section


open TensorProduct

/-- Condition (1): The map `Spec(S) → Spec(R)` induced by `φ` is surjective. -/
def SpecSurjective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) : Prop :=
  Function.Surjective (PrimeSpectrum.comap φ)

/-- Condition (2): For every ideal `I` of `R`, the contraction of the radical of
the extension `I S` equals the radical of `I`. -/
def RadicalContractionEq {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) : Prop :=
  ∀ I : Ideal R, Ideal.comap φ (Ideal.map φ I).radical = I.radical

/-- Condition (3): For every radical ideal `I` of `R`, the contraction of the
extension `I S` equals `I`. -/
def RadicalIdealContractionEq {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) : Prop :=
  ∀ I : Ideal R, I.IsRadical → Ideal.comap φ (Ideal.map φ I) = I

/-- Condition (4): For every prime ideal `𝔭` of `R`, the contraction of the
extension `𝔭 S` equals `𝔭`. -/
def PrimeContractionEq {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) : Prop :=
  ∀ 𝔭 : Ideal R, 𝔭.IsPrime → Ideal.comap φ (Ideal.map φ 𝔭) = 𝔭

/-! ### Main implications -/

/-- (1) ⟹ (2): If `Spec(S) → Spec(R)` is surjective, then for any ideal `I` of `R`,
the contraction of `√(IS)` is `√I`. -/
theorem radicalContractionEq_of_specSurjective
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    SpecSurjective φ → RadicalContractionEq φ := by
  intro hsurj I
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap] at hx
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro 𝔭 ⟨hI𝔭, h𝔭prime⟩
    obtain ⟨q, hq⟩ := hsurj ⟨𝔭, h𝔭prime⟩
    have hcomap : Ideal.comap φ q.asIdeal = 𝔭 := congrArg PrimeSpectrum.asIdeal hq
    have hmap_le : Ideal.map φ I ≤ q.asIdeal := by
      rwa [Ideal.map_le_iff_le_comap, hcomap]
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
    rw [← hcomap]
    exact q.isPrime.mem_of_pow_mem n (hmap_le hn)
  · rw [Ideal.comap_radical]
    exact Ideal.radical_mono Ideal.le_comap_map

/-- (2) ⟹ (3): If contraction commutes with radical-of-extension for all ideals,
then contraction of the extension equals the ideal for every radical ideal. -/
theorem radicalIdealContractionEq_of_radicalContractionEq
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    RadicalContractionEq φ → RadicalIdealContractionEq φ := by
  intro h2 I hIrad
  exact le_antisymm ((Ideal.comap_mono Ideal.le_radical).trans ((h2 I).trans hIrad.radical).le)
    Ideal.le_comap_map

/-- (3) ⟹ (4): If contraction of extension equals the ideal for every radical ideal,
then in particular for every prime ideal. -/
theorem primeContractionEq_of_radicalIdealContractionEq
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    RadicalIdealContractionEq φ → PrimeContractionEq φ :=
  fun h3 𝔭 h𝔭 => h3 𝔭 h𝔭.isRadical

/-- (4) ⟹ (1): If contraction of `𝔭 S` is `𝔭` for every prime `𝔭`, then
`Spec(S) → Spec(R)` is surjective. -/
theorem specSurjective_of_primeContractionEq
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    PrimeContractionEq φ → SpecSurjective φ :=
  fun h p => (PrimeSpectrum.mem_range_comap_iff φ).mpr (h _ p.isPrime)

/-- Main equivalence: conditions (1), (2), (3), (4) are equivalent. -/
@[stacks 00FI]
theorem main_equivalence
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    (SpecSurjective φ ↔ RadicalContractionEq φ) ∧
    (RadicalContractionEq φ ↔ RadicalIdealContractionEq φ) ∧
    (RadicalIdealContractionEq φ ↔ PrimeContractionEq φ) ∧
    (PrimeContractionEq φ ↔ SpecSurjective φ) :=
  have h12 := radicalContractionEq_of_specSurjective φ
  have h23 := radicalIdealContractionEq_of_radicalContractionEq φ
  have h34 := primeContractionEq_of_radicalIdealContractionEq φ
  have h41 := specSurjective_of_primeContractionEq φ
  ⟨⟨h12, fun h ↦ h41 (h34 (h23 h))⟩, ⟨h23, fun h ↦ h12 (h41 (h34 h))⟩,
    ⟨h34, fun h ↦ h23 (h12 (h41 h))⟩, ⟨h41, fun h ↦ h34 (h23 (h12 h))⟩⟩

/-! ### Base change

We show that conditions (1), (2), (3) are preserved under base change along
any ring map `R →+* R'`. The key step is preserving condition (1):
given `q : Spec(S)` over `p := comap ψ p'`, the residue field at `p'`
satisfies `κ(p') ⊗[R] S ≃ κ(p') ⊗[κ(p)] (κ(p) ⊗[R] S)`, and the latter is
nontrivial since `κ(p) ⊗[R] S` is nontrivial (by Spec-surjectivity of `φ` and
the fiber characterization) and `κ(p')` is faithfully flat over `κ(p)`.
-/

/-- Base change preserves Spec-surjectivity. -/
@[sga "1 VIII 3.1" "special case"]
theorem base_change_preserves_specSurjective
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (φ : R →+* S) (ψ : R →+* R') :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra R R' := ψ.toAlgebra
    SpecSurjective φ →
    SpecSurjective (Algebra.TensorProduct.includeLeftRingHom :
      R' →+* TensorProduct R R' S) := by
  intro hφ p'
  let algRS : Algebra R S := φ.toAlgebra
  let algRR' : Algebra R R' := ψ.toAlgebra
  -- Use Mathlib's characterization of range via nontriviality of fiber.
  show p' ∈ Set.range (PrimeSpectrum.comap (algebraMap R' (TensorProduct R R' S)))
  rw [← PrimeSpectrum.nontrivial_iff_mem_rangeComap]
  -- Identify the fiber `κ(p') ⊗[R'] (R' ⊗[R] S)` with `κ(p') ⊗[R] S`.
  let E : (p'.asIdeal.ResidueField ⊗[R'] (TensorProduct R R' S)) ≃ₐ[R']
      (p'.asIdeal.ResidueField ⊗[R] S) :=
    Algebra.TensorProduct.cancelBaseChange R R' R' p'.asIdeal.ResidueField S
  -- Reduce `Nontrivial (LHS)` to `Nontrivial (RHS)` via the algebra equivalence.
  suffices h : Nontrivial (p'.asIdeal.ResidueField ⊗[R] S) from
    E.symm.toEquiv.injective.nontrivial
  -- Set `p := comap ψ p'` and pick `q` over `p` via Spec-surjectivity of `φ`.
  set p : PrimeSpectrum R := PrimeSpectrum.comap ψ p'
  obtain ⟨q, hq⟩ := hφ p
  have hp_p' : p.asIdeal = p'.asIdeal.comap (algebraMap R R') := rfl
  -- Set residue fields.
  let k : Type _ := p.asIdeal.ResidueField
  let kp' : Type _ := p'.asIdeal.ResidueField
  -- Step 1: `Nontrivial (k ⊗[R] S)` via `nontrivial_iff_mem_rangeComap` applied
  -- to φ at the prime p.
  have hk_S_nontriv : Nontrivial (k ⊗[R] S) :=
    PrimeSpectrum.nontrivial_iff_mem_rangeComap p |>.mpr ⟨q, hq⟩
  -- Step 2: equip `kp'` with a `k`-algebra structure via the residue-field map
  -- κ(p) → κ(p').
  -- The residue-field map κ(p) → κ(p') as an R-algebra hom.
  let resMap : k →ₐ[R] kp' :=
    Ideal.ResidueField.mapₐ (R := R) p.asIdeal p'.asIdeal (Algebra.ofId R R') hp_p'
  let algKKp' : Algebra k kp' := resMap.toRingHom.toAlgebra
  -- The scalar tower R → k → kp' holds because `resMap` is an R-algebra hom.
  have tower_R_k_kp' : IsScalarTower R k kp' :=
    IsScalarTower.of_algebraMap_eq (fun r => (resMap.commutes r).symm)
  -- Step 3: identify `kp' ⊗[R] S ≃ₐ[kp'] kp' ⊗[k] (k ⊗[R] S)` via cancelBaseChange.
  let F : (kp' ⊗[k] (k ⊗[R] S)) ≃ₐ[kp']
      (kp' ⊗[R] S) :=
    Algebra.TensorProduct.cancelBaseChange R k kp' kp' S
  -- Transport `Nontrivial` along the algebra equivalence F.
  suffices h' : Nontrivial (kp' ⊗[k] (k ⊗[R] S)) from
    F.toEquiv.injective.nontrivial
  -- Step 4: `kp'` is faithfully flat over `k` (it is a field extension, hence
  -- a free `k`-module). Therefore tensoring with `kp'` preserves nontriviality.
  have : Module.Free k kp' := Module.Free.of_divisionRing k kp'
  exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
    (R := k) (M := kp') (N := k ⊗[R] S)).mpr hk_S_nontriv

/-- Spec-surjectivity of `φ` gives condition (2) for the base-changed map. -/
private theorem base_change_radicalContractionEq_of_specSurjective
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (φ : R →+* S) (ψ : R →+* R') :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra R R' := ψ.toAlgebra
    SpecSurjective φ →
    RadicalContractionEq (Algebra.TensorProduct.includeLeftRingHom :
      R' →+* TensorProduct R R' S) :=
  fun h => radicalContractionEq_of_specSurjective _ (base_change_preserves_specSurjective φ ψ h)

/-- Condition (2) is stable under base change along `ψ : R →+* R'`. -/
theorem base_change_preserves_radicalContractionEq
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (φ : R →+* S) (ψ : R →+* R') :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra R R' := ψ.toAlgebra
    RadicalContractionEq φ →
    RadicalContractionEq (Algebra.TensorProduct.includeLeftRingHom :
      R' →+* TensorProduct R R' S) :=
  fun h2 => base_change_radicalContractionEq_of_specSurjective φ ψ ((main_equivalence φ).1.2 h2)

/-- Condition (3) is stable under base change along `ψ : R →+* R'`. -/
theorem base_change_preserves_radicalIdealContractionEq
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (φ : R →+* S) (ψ : R →+* R') :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra R R' := ψ.toAlgebra
    RadicalIdealContractionEq φ →
    RadicalIdealContractionEq (Algebra.TensorProduct.includeLeftRingHom :
      R' →+* TensorProduct R R' S) :=
  fun h3 => (main_equivalence _).2.1.1 <|
    base_change_radicalContractionEq_of_specSurjective φ ψ <| (main_equivalence φ).2.2.2.1 <|
      primeContractionEq_of_radicalIdealContractionEq φ h3

/-- Conditions (1), (2), (3) are equivalent for the base-changed map. -/
theorem base_change_equivalence
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (φ : R →+* S) (ψ : R →+* R') :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra R R' := ψ.toAlgebra
    (SpecSurjective (Algebra.TensorProduct.includeLeftRingHom :
        R' →+* TensorProduct R R' S) ↔
      RadicalContractionEq (Algebra.TensorProduct.includeLeftRingHom :
        R' →+* TensorProduct R R' S)) ∧
    (RadicalContractionEq (Algebra.TensorProduct.includeLeftRingHom :
        R' →+* TensorProduct R R' S) ↔
      RadicalIdealContractionEq (Algebra.TensorProduct.includeLeftRingHom :
        R' →+* TensorProduct R R' S)) :=
  ⟨(main_equivalence _).1, (main_equivalence _).2.1⟩

-- ===== merged from StacksDraft.Ch10.Sec30.Tag00FJ =====



/-!
# Image of `Spec` is dense iff the ring map is injective (domain case)

For a domain `R` and a ring map `φ : R → S`, the following are equivalent:
injectivity of `φ`, density of the range of `Spec(S) → Spec(R)`, and the
existence of a prime of `S` whose contraction to `R` is the zero ideal.
-/


open PrimeSpectrum

variable (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] (φ : R →+* S)

/-- (1) → (3): If `φ : R →+* S` is injective and `R` is a domain, then there exists a prime
`q` of `S` whose contraction to `R` is the zero ideal `⊥`. -/
private lemma inj_imp_exists_prime_bot (hφ : Function.Injective φ) :
    ∃ q : PrimeSpectrum S, (PrimeSpectrum.comap φ q).asIdeal = ⊥ := by
  -- The multiplicative subset `M = φ(R \ {0})` of `S` is disjoint from `(⊥ : Ideal S)`.
  set M : Submonoid S := (nonZeroDivisors R).map φ
  have hdisj : Disjoint ((⊥ : Ideal S) : Set S) (M : Set S) := by
    rw [show ((⊥ : Ideal S) : Set S) = {0} from rfl, Set.disjoint_singleton_left]
    rintro ⟨r, hr, hr0⟩
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) (hφ (by simpa using hr0))
  obtain ⟨q, hqp, _, hqdisj⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal S) M hdisj
  refine ⟨⟨q, hqp⟩, eq_bot_iff.mpr fun r hr => ?_⟩
  rw [Submodule.mem_bot]
  by_contra h
  exact Set.disjoint_left.mp hqdisj hr ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr h, rfl⟩

/-- (3) → (2): If there exists a prime `q` of `S` with `(comap φ q).asIdeal = ⊥`, then the
range of `PrimeSpectrum.comap φ` is dense in `PrimeSpectrum R`. -/
private lemma exists_prime_bot_imp_dense
    (h : ∃ q : PrimeSpectrum S, (PrimeSpectrum.comap φ q).asIdeal = ⊥) :
    Dense (Set.range (PrimeSpectrum.comap φ)) := by
  obtain ⟨q, hq⟩ := h
  -- The singleton `{⟨⊥⟩}` is dense in `PrimeSpectrum R` for a domain.
  have hdense : Dense ({⟨⊥, Ideal.isPrime_bot⟩} : Set (PrimeSpectrum R)) := fun _ => by
    rw [PrimeSpectrum.closure_singleton]
    simp
  exact hdense.mono (Set.singleton_subset_iff.mpr ⟨q, PrimeSpectrum.ext hq⟩)

/-- (2) → (1): If the range of `PrimeSpectrum.comap φ` is dense in `PrimeSpectrum R`, then
`φ` is injective. -/
private lemma dense_imp_inj (hd : Dense (Set.range (PrimeSpectrum.comap φ))) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hne
  -- The basic open `D(r)` contains the generic point `⟨⊥⟩`, hence is nonempty.
  have h0 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ (basicOpen r).carrier := by
    show r ∉ (⊥ : Ideal R)
    rwa [Ideal.mem_bot]
  obtain ⟨_, ⟨q, rfl⟩, hp_open⟩ := hd.exists_mem_open (basicOpen r).is_open' ⟨_, h0⟩
  exact hp_open (show φ r ∈ q.asIdeal by rw [hr]; exact q.asIdeal.zero_mem)

/-- Let `R` be a domain and `φ : R →+* S` a ring map. Then the following are equivalent:
1. `φ` is injective.
2. The range of the induced map `PrimeSpectrum.comap φ` is dense in `PrimeSpectrum R`.
3. There exists a prime `q` of `S` whose preimage under `φ` is the zero ideal of `R`. -/
@[stacks 00FJ, ega "0 2.1.5" "special case", ega "I 1.2.7" "special case"]
theorem domain_image_dense_set_points_generic_point_tfae :
    List.TFAE
      [ Function.Injective φ
      , Dense (Set.range (PrimeSpectrum.comap φ))
      , ∃ q : PrimeSpectrum S, (PrimeSpectrum.comap φ q).asIdeal = ⊥ ] := by
  tfae_have 1 → 3 := inj_imp_exists_prime_bot R S φ
  tfae_have 3 → 2 := exists_prime_bot_imp_dense R S φ
  tfae_have 2 → 1 := dense_imp_inj R S φ
  tfae_finish

/-!
### Minimal primes and the image of `Spec`

Mathlib states the two remaining tags of this file.

Stacks 00FK — for an injective ring map, `Spec(S) → Spec(R)` hits every minimal prime of `R` —
is `Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`, stated with the prime of `S`
produced as an ideal rather than as a point of `PrimeSpectrum S`. It already carries the tag
upstream, so nothing is recorded for it here.

Stacks 0CAN — a minimal prime of `R` lying in the image of `Spec(S) → Spec(R)` is the image of
a minimal prime of `S` — is `Ideal.exists_minimalPrimes_comap_eq` at `I = ⊥`, whose hypothesis
that `p` be minimal over `f⁻¹(⊥)` is what the tag's two hypotheses together say.
-/

add_to_stacks 0CAN "at `I = ⊥`, where minimality over `f⁻¹(⊥)` is the tag's hypothesis that `p`
  be a minimal prime lying in the image" Ideal.exists_minimalPrimes_comap_eq
add_to_ega "0 1.5.8" Ideal.exists_minimalPrimes_comap_eq

