module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularComplementFacts
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.KummerCodimensionOne
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.KummerSubalgebra
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.KummerUnramified
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.StrictlyHenselianPurity
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abhyankar's lemma over a strictly henselian regular local ring: the connected case

Let `A` be a strictly henselian regular local ring and `φ ∈ 𝔪_A` a nonzero element with `A/φA`
regular. Let `B` be a finite étale `A_φ`-algebra which is a domain and which is tamely ramified
over `Spec A` in codimension one. Then `B ≅ A[x]/(x^d - φ)_φ` over `A_φ` for some `d ≥ 1`
invertible in `A`. This is the main step of the proof of Abhyankar's lemma for a regular divisor
([Stacks, Tag 0EYG]).

## Main results

* `AlgebraicGeometry.Abhyankar.exists_ringEquiv_of_isDomain`: the statement above, granted purity
  for regular local rings.

## Implementation notes

The proof follows the source. With `e` a common multiple, invertible in `κ((φ))`, of the
ramification indices of the fraction field of `B` over the discrete valuation ring `A_{(φ)}`, the
cover becomes unramified in codimension one over `A' = A[x]/(x^e - φ)` (Abhyankar's lemma,
`AlgebraicGeometry.Abhyankar.isUnramifiedWithRespectTo_of_tensor`), hence has a section over
`A'_x` (`AlgebraicGeometry.Abhyankar.nonempty_algHom_of_isUnramifiedInCodimensionOne`, which uses
purity). So `B` embeds into `K[φ^{1/e}]`, and
`AlgebraicGeometry.Abhyankar.exists_ringEquiv_of_ringHom_K1` identifies it; the exponent is a unit
by `AlgebraicGeometry.Abhyankar.isUnit_natCast_of_etale` and
`AlgebraicGeometry.Abhyankar.isUnit_of_isUnit_algebraMap_away`.

## References

* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial Stacks.KummerExtension
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Abhyankar

/-- A subalgebra of a fraction field `L` of `B` which is algebraic over `K` and contains the image
of `B` is everything. -/
private theorem _root_.Subalgebra.eq_top_of_algebraMap_mem {K B L : Type*} [Field K] [CommRing B]
    [IsDomain B] [Field L] [Algebra K L] [Algebra B L] [IsFractionRing B L] (S : Subalgebra K L)
    (halg : ∀ x ∈ S, IsAlgebraic K x) (hS : ∀ b, algebraMap B L b ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro l _
  obtain ⟨b₁, b₂, -, rfl⟩ := IsFractionRing.div_surjective (A := B) l
  rw [div_eq_mul_inv]
  exact S.mul_mem (hS b₁)
    (Subalgebra.inv_mem_of_algebraic (A := S) (x := ⟨_, hS b₂⟩) (halg _ (hS b₂)))

/-- **The fraction field of a finite étale domain is finite separable.** If `B` is a domain finite
étale over the domain `R`, `K` is a field over `R` and `L` a fraction field of `B` over `K`, then
`L/K` is finite separable: `L` is a quotient of the finite étale `K`-algebra `K ⊗_R B`. -/
@[sga "3 VIIB 1.6.E" "special case"]
theorem finiteDimensional_and_isSeparable_of_etale {R B K L : Type u} [CommRing R] [CommRing B]
    [IsDomain B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B] [Field K] [Field L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra B L]
    [IsScalarTower R B L] [IsFractionRing B L] :
    FiniteDimensional K L ∧ Algebra.IsSeparable K L := by
  let g : K ⊗[R] B →ₐ[K] L := Algebra.TensorProduct.lift (Algebra.ofId K L)
    (IsScalarTower.toAlgHom R B L) (fun _ _ ↦ Commute.all _ _)
  have hgB : ∀ b : B, g (1 ⊗ₜ b) = algebraMap B L b := by
    intro b
    simp [g, Algebra.TensorProduct.lift_tmul]
  have : Module.Finite K g.range := Module.Finite.range g.toLinearMap
  have hsurj : Function.Surjective g := (AlgHom.range_eq_top g).mp <|
    g.range.eq_top_of_algebraMap_mem (B := B) (fun x hx ↦
      (Algebra.IsAlgebraic.isAlgebraic (R := K) (⟨x, hx⟩ : g.range)).algHom g.range.val)
      fun b ↦ ⟨1 ⊗ₜ b, hgB b⟩
  have : Module.Finite K L := Module.Finite.of_surjective g.toLinearMap hsurj
  have : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_surjective g hsurj
  exact ⟨inferInstance, Algebra.FormallyUnramified.isSeparable K L⟩

/-- If `e ≥ 1` is invertible in a field `k`, then so is some multiple `e' ≥ 2` of `e`. -/
private theorem exists_two_le_isUnit_natCast_of_dvd {k : Type*} [Field k] {e : ℕ} (he : 1 ≤ e)
    (hu : IsUnit (e : k)) : ∃ e' : ℕ, 2 ≤ e' ∧ IsUnit (e' : k) ∧ e ∣ e' := by
  obtain ⟨n, hn, hun⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : k) := by
    by_cases h2 : IsUnit (2 : k)
    · exact ⟨2, le_rfl, h2⟩
    · refine ⟨3, by omega, isUnit_iff_ne_zero.mpr ?_⟩
      have h20 : (2 : k) = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using h2
      intro h30
      exact one_ne_zero (by linear_combination h30 - h20 : (1 : k) = 0)
  exact ⟨n * e, by nlinarith, by simpa using hun.mul hu, dvd_mul_left e n⟩

/-- For a tamely ramified finite separable extension `L/K` of the fraction field of a discrete
valuation ring `A`, there is a common multiple `e₀ ≥ 1` of the ramification indices of the maximal
ideals of the integral closure which is invertible in the residue field of `A`. -/
private theorem exists_isUnit_forall_ramificationIdx'_dvd (A K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (htame : IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo A K L) :
    ∃ e₀ : ℕ, 1 ≤ e₀ ∧ IsUnit (e₀ : ResidueField A) ∧ ∀ m : Ideal (integralClosure A L),
      m.IsMaximal → m.LiesOver (maximalIdeal A) →
        Ideal.ramificationIdx' (maximalIdeal A) m ∣ e₀ := by
  classical
  let B := integralClosure A L
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have hinj : Function.Injective (algebraMap A B) := by
    intro x y h
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa [IsScalarTower.algebraMap_apply A K L] using congrArg Subtype.val h
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hpne : maximalIdeal A ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  let S : Set (Ideal B) := {m | m.IsMaximal ∧ m.LiesOver (maximalIdeal A)}
  have hS : S.Finite := (IsDedekindDomain.primesOver_finite (maximalIdeal A) B).subset
    fun m hm => ⟨hm.1.isPrime, hm.2⟩
  refine ⟨∏ m ∈ hS.toFinset, Ideal.ramificationIdx' (maximalIdeal A) m, ?_, ?_, ?_⟩
  · refine Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun m hm => ?_)
    obtain ⟨hmax, hlies⟩ := hS.mem_toFinset.mp hm
    have := hmax.isPrime
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m hpne
  · rw [Nat.cast_prod, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.mpr fun m hm => ?_
    obtain ⟨hmax, hlies⟩ := hS.mem_toFinset.mp hm
    have := hmax.isPrime
    have hne := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m hpne
    obtain ⟨-, hchar⟩ := htame m hmax hlies
    intro h0
    have hdvd := (ringChar.spec (ResidueField A) _).mp h0
    change ringChar (A ⧸ maximalIdeal A) = 0 ∨
      Nat.Coprime (ringChar (A ⧸ maximalIdeal A)) _ at hchar
    change ringChar (A ⧸ maximalIdeal A) ∣ _ at hdvd
    rcases hchar with h | h
    · rw [h, zero_dvd_iff] at hdvd
      exact hne hdvd
    · exact CharP.ringChar_ne_one (Nat.Coprime.eq_one_of_dvd h hdvd)
  · intro m hmax hlies
    exact Finset.dvd_prod_of_mem _ (hS.mem_toFinset.mpr ⟨hmax, hlies⟩)

/-- If `e` is invertible in the residue field of a local ring `A`, then the residue characteristic
is zero or coprime to `e`. -/
private theorem ringChar_eq_zero_or_coprime_of_isUnit {A : Type*} [CommRing A] [IsLocalRing A]
    {e : ℕ} (he : IsUnit (e : ResidueField A)) :
    ringChar (A ⧸ maximalIdeal A) = 0 ∨ Nat.Coprime (ringChar (A ⧸ maximalIdeal A)) e := by
  show ringChar (ResidueField A) = 0 ∨ Nat.Coprime (ringChar (ResidueField A)) e
  rcases CharP.char_is_prime_or_zero (ResidueField A) (ringChar (ResidueField A)) with hp | hp
  · right
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    rw [(ringChar.spec (ResidueField A) e).mpr hdvd] at he
    exact not_isUnit_zero he
  · exact Or.inl hp

/-- The localization `A_φ` of an integrally closed domain at a nonzero element is a normal ring. -/
private theorem isNormalRing_localization_away {A : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] {φ : A} (hφ0 : φ ≠ 0) : IsNormalRing (Localization.Away φ) := by
  have : IsDomain (Localization.Away φ) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hφ0)
  have : IsIntegrallyClosed (Localization.Away φ) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away φ) (Submonoid.powers φ)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hφ0)
  intro P _
  exact ⟨IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors,
    isIntegrallyClosed_of_isLocalization _ P.primeCompl P.primeCompl_le_nonZeroDivisors⟩

/-- If `e` is invertible in the residue field of the localization `O` of `A` at a prime `P`, then
no divisor of `e` lies in `P`. -/
private theorem natCast_notMem_of_dvd_of_isUnit_residueField {A O : Type*} [CommRing A] [CommRing O]
    [IsLocalRing O] [Algebra A O] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime O P]
    {d e : ℕ} (hde : d ∣ e) (hue : IsUnit (e : ResidueField O)) : (d : A) ∉ P := by
  intro h
  have hdO : algebraMap A O d ∈ maximalIdeal O := by
    rw [← Ideal.mem_comap]
    show _ ∈ (maximalIdeal O).under A
    rwa [IsLocalization.AtPrime.under_maximalIdeal (S := O) P]
  rw [map_natCast] at hdO
  have : IsUnit (d : ResidueField O) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hde) hue
  rw [← map_natCast (residue O), (IsLocalRing.residue_eq_zero_iff _).mpr hdO] at this
  exact not_isUnit_zero this

/-- The localization `O` of a domain `A` at a prime principal ideal `(φ)` with `φ ≠ 0`, if
Noetherian, is a discrete valuation ring with uniformizer `φ`. -/
private theorem isDiscreteValuationRing_and_irreducible_of_isLocalization_atPrime_span {A O : Type*}
    [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [Algebra A O] {φ : A} (hφ0 : φ ≠ 0) [(Ideal.span {φ}).IsPrime]
    [IsLocalization.AtPrime O (Ideal.span {φ})] :
    IsDiscreteValuationRing O ∧ Irreducible (algebraMap A O φ) := by
  have hAO : Function.Injective (algebraMap A O) :=
    IsLocalization.injective O (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {φ}))
  have hmO : maximalIdeal O = Ideal.span {algebraMap A O φ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {φ}) O, Ideal.map_span,
      Set.image_singleton]
  have hφO : algebraMap A O φ ≠ 0 := (map_ne_zero_iff _ hAO).mpr hφ0
  obtain ⟨_, hOdvr, hπirr⟩ := IsLocalRing.isDiscreteValuationRing_of_maximalIdeal_eq_span hmO
    (isSMulRegular_iff_right_eq_zero_of_smul.mpr fun c hc ↦
      (mul_eq_zero.mp hc).resolve_left hφO)
  exact ⟨hOdvr, hπirr⟩

/-- **Abhyankar's lemma over a strictly henselian regular local ring, connected case.** Let `A`
be a strictly henselian regular local ring, `0 ≠ φ ∈ 𝔪_A` with `A/φA` regular, and `B` a finite
étale `A_φ`-algebra which is a domain and is tamely ramified over `Spec A` in codimension one.
Then `B ≅ A[x]/(x^d - φ)_φ` over `A_φ` for some `d ≥ 1` invertible in `A`. The argument `h0BMA` is
purity for regular local rings ([Stacks, Tag 0BMA] (1)). -/
theorem exists_ringEquiv_of_isDomain (h0BMA : PurityAtRegularLocalRings.{u})
    (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A] [IsRegularLocalRing A]
    (φ : A) (hφ : φ ∈ maximalIdeal A) (hφ0 : φ ≠ 0)
    (hreg : IsRegularLocalRing (A ⧸ Ideal.span {φ}))
    (B : Type u) [CommRing B] [IsDomain B] [Algebra (Localization.Away φ) B]
    [Module.Finite (Localization.Away φ) B] [Algebra.Etale (Localization.Away φ) B]
    (htame : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen φ))
      (AffineFieldFactors.coverMap (R := .of A) φ B)) :
    ∃ d : ℕ, 0 < d ∧ IsUnit (d : A) ∧ ∃ σ : Localization.Away
        (algebraMap A (standardTamelyRamifiedAlgebra A φ d) φ) ≃+* B,
      ∀ r, σ (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A φ d)) φ r) =
        algebraMap _ B r := by
  classical
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsDomain (A ⧸ Ideal.span {φ}) := IsRegularLocalRing.isDomain _
  have hp : (Ideal.span {φ}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have : IsDomain (Localization.Away φ) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hφ0)
  -- The point `ξ = (φ)` and its local ring `O`, a discrete valuation ring with uniformizer `φ`.
  let ξ : Spec (.of A) := ⟨Ideal.span {φ}, hp⟩
  let O := (Spec (.of A)).presheaf.stalk ξ
  let : Algebra A O := StructureSheaf.stalkAlgebra A ξ
  have : IsLocalization.AtPrime O (Ideal.span {φ}) := StructureSheaf.IsLocalization.to_stalk A ξ
  have : IsNoetherianRing O := IsLocalization.isNoetherianRing (Ideal.span {φ}).primeCompl O
    inferInstance
  have : IsDomain O :=
    IsLocalization.isDomain_of_le_nonZeroDivisors O (M := (Ideal.span {φ}).primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {φ}))
  obtain ⟨_, hπirr⟩ :=
    isDiscreteValuationRing_and_irreducible_of_isLocalization_atPrime_span (O := O) hφ0
  -- The fraction fields `K` of `A` (and `O`) and `L` of `B`.
  let K := FractionRing A
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hOK : ∀ s : (Ideal.span {φ}).primeCompl, IsUnit (algebraMap A K s) := fun s ↦
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hAK).mpr fun h ↦ s.2 (h ▸ Ideal.zero_mem _))
  let : Algebra O K := (IsLocalization.lift hOK).toAlgebra
  have : IsScalarTower A O K := IsScalarTower.of_algebraMap_eq fun a ↦
    (IsLocalization.lift_eq hOK a).symm
  have : IsFractionRing O K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {φ}).primeCompl O K
  have hφK : IsUnit (algebraMap A K φ) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hAK).mpr hφ0)
  let : Algebra (Localization.Away φ) K := (IsLocalization.Away.lift φ hφK).toAlgebra
  have : IsScalarTower A (Localization.Away φ) K := IsScalarTower.of_algebraMap_eq fun a ↦
    (IsLocalization.Away.lift_eq φ hφK a).symm
  have hRB : Function.Injective (algebraMap (Localization.Away φ) B) :=
    Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  have hAR : Function.Injective (algebraMap A (Localization.Away φ)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hφ0)
  let ιA : A →+* B := (algebraMap (Localization.Away φ) B).comp (algebraMap A (Localization.Away φ))
  have hιA : Function.Injective ιA := hRB.comp hAR
  let L := FractionRing B
  let : Algebra A L := ((algebraMap B L).comp ιA).toAlgebra
  have : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr
    ((IsFractionRing.injective B L).comp hιA)
  let : Algebra K L := FractionRing.liftAlgebra A L
  let : Algebra O L := ((algebraMap K L).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Localization.Away φ) K L := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext (Submonoid.powers φ)
      (RingHom.ext fun a ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Localization.Away φ) B L,
      ← IsScalarTower.algebraMap_apply A (Localization.Away φ) K,
      ← IsScalarTower.algebraMap_apply A K L]
    rfl
  obtain ⟨hLfin, hLsep⟩ := finiteDimensional_and_isSeparable_of_etale
    (R := Localization.Away φ) (B := B) (K := K) (L := L)
  have hBL : ∀ a : A, algebraMap B L (algebraMap _ B (algebraMap A (Localization.Away φ) a)) =
      algebraMap O L (algebraMap A O a) := by
    intro a
    show _ = algebraMap K L (algebraMap O K (algebraMap A O a))
    rw [← IsScalarTower.algebraMap_apply A O K, ← IsScalarTower.algebraMap_apply A K L]
    rfl
  -- `L` is a field factor of the cover at `ξ`, so it is tamely ramified over `O`.
  have hFF : Stacks.FundamentalGroup.IsFieldFactorAt
      (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen φ))
      (AffineFieldFactors.coverMap (R := .of A) φ B) ξ K L := by
    refine AffineFieldFactors.isFieldFactorAt_of_ringHom (R := .of A) ξ ?_
      (by rwa [← IsScalarTower.algebraMap_apply]) (algebraMap B L) ?_ ?_
    · rw [Spec.fromSpecStalk_eq']
      rfl
    · exact fun r ↦ hBL r
    · have : Module.Finite K L := hLfin
      exact Subalgebra.eq_top_of_algebraMap_mem (B := B) _
        (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x) fun b ↦ Algebra.subset_adjoin ⟨b, rfl⟩
  have hdim : ringKrullDim O = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one O
  obtain ⟨Z, hZ⟩ := exists_primeDivisor_genericPoint_eq ξ hdim
  have hξU : ξ ∉ Set.range
      (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen φ)).base := by
    rintro ⟨y, hy⟩
    have hy' : y.1 = ξ := hy
    have h2 := y.2
    rw [hy'] at h2
    exact h2 (Ideal.mem_span_singleton_self φ)
  have htame' := htame Z (by rwa [hZ])
  rw [hZ] at htame'
  have hLtame : IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo O K L :=
    htame' inferInstance inferInstance K L hFF
  -- A common exponent `e ≥ 2`, invertible in `κ(ξ)`, for the ramification indices of `L`.
  obtain ⟨e₀, he₀, hu₀, hdiv₀⟩ := exists_isUnit_forall_ramificationIdx'_dvd O K L hLtame
  obtain ⟨e, he2, hue, hdive⟩ := exists_two_le_isUnit_natCast_of_dvd he₀ hu₀
  have : NeZero e := ⟨by omega⟩
  have hreg' : ∀ d : ℕ, 0 < d → IsRegularLocalRing (standardTamelyRamifiedAlgebra A φ d) :=
    fun d hd ↦ have : NeZero d := ⟨hd.ne'⟩; isRegularLocalRing A d hφ hφ0 hreg
  -- The Kummer algebra `A' = A[x]/(x^e - φ)`.
  let A' := standardTamelyRamifiedAlgebra A φ e
  have : IsLocalRing A' := isLocalRing A e hφ
  have : IsRegularLocalRing A' := hreg' e (by omega)
  have : StrictlyHenselianLocalRing A' := strictlyHenselianLocalRing A e hφ
  have : IsDomain A' := IsRegularLocalRing.isDomain A'
  let g : A' := algebraMap A A' φ
  have hg0 : g ≠ 0 := by
    show algebraMap A A' φ ≠ 0
    rw [← root_pow]
    exact pow_ne_zero e (nonZeroDivisors.ne_zero (root_mem_nonZeroDivisors A e hφ0))
  let Cφ := Localization.Away g
  let : Algebra (Localization.Away φ) Cφ := (Localization.awayMap (algebraMap A A') φ).toAlgebra
  have hκ : ∀ a, algebraMap (Localization.Away φ) Cφ (algebraMap A _ a) =
      algebraMap A' Cφ (algebraMap A A' a) := by
    intro a
    show Localization.awayMap (algebraMap A A') φ _ = _
    exact IsLocalization.map_eq _ _
  let B' := Cφ ⊗[Localization.Away φ] B
  -- The base change is unramified over `Spec A'` in codimension one.
  have hunr := isUnramifiedInCodimensionOne_baseChange (A := A) hφ0 (e := e) hLtame hue
    (fun m hm hlo ↦ (hdiv₀ m hm hlo).trans hdive) B hBL
  -- The Kummer field `K[φ^{1/e}]` and the map `A'_φ → K[φ^{1/e}]`.
  have : Fact (Irreducible (kummerPoly K (algebraMap A O φ) e)) :=
    ⟨kummerPoly_irreducible K _ e (by omega) hπirr⟩
  let K1 := K1 K (algebraMap A O φ) e
  have hpiRoot : piRoot K (algebraMap A O φ) e ^ e = algebraMap K K1 (algebraMap A K φ) := by
    rw [piRoot_pow, IsScalarTower.algebraMap_apply O K K1, ← IsScalarTower.algebraMap_apply A O K]
  let gK1 : A →+* K1 := (algebraMap K K1).comp (algebraMap A K)
  let χ₀ : A' →+* K1 := Ideal.Quotient.lift _ (Polynomial.eval₂RingHom gK1
    (piRoot K (algebraMap A O φ) e)) (by
      intro p hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      simp [gK1, hpiRoot])
  have hχ₀A : ∀ a, χ₀ (algebraMap A A' a) = gK1 a := by
    intro a
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_eq]
    show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk]
    simp
  have hχ₀u : IsUnit (χ₀ g) := by
    rw [hχ₀A]
    exact hφK.map (algebraMap K K1)
  let χ : Cφ →+* K1 := IsLocalization.Away.lift g hχ₀u
  have hχ : ∀ c, χ (algebraMap A' _ c) = χ₀ c := IsLocalization.Away.lift_eq g hχ₀u
  have hχR : ∀ a, χ (algebraMap (Localization.Away φ) Cφ (algebraMap A _ a)) = gK1 a := by
    intro a
    rw [hκ, hχ, hχ₀A]
  -- `B'` is nontrivial: it maps to `K[φ^{1/e}] ⊗_K L`.
  have : Nontrivial B' := by
    let N := K1 ⊗[K] L
    have hK1R : ∀ r, algebraMap (Localization.Away φ) K1 r =
        algebraMap K K1 (algebraMap (Localization.Away φ) K r) :=
      IsScalarTower.algebraMap_apply (Localization.Away φ) K K1
    have hf₁ : χ.comp (algebraMap (Localization.Away φ) Cφ) =
        algebraMap (Localization.Away φ) K1 :=
      IsLocalization.ringHom_ext (Submonoid.powers φ) (RingHom.ext fun a ↦ by
        simp only [RingHom.comp_apply]
        rw [hχR, hK1R, ← IsScalarTower.algebraMap_apply A (Localization.Away φ) K]
        rfl)
    let f₁ : Cφ →ₐ[Localization.Away φ] N :=
      { (Algebra.TensorProduct.includeLeftRingHom).comp χ with
        commutes' := fun r ↦ by
          show χ (algebraMap _ Cφ r) ⊗ₜ (1 : L) = _
          rw [← RingHom.comp_apply, hf₁, Algebra.TensorProduct.algebraMap_apply] }
    let f₂ : B →ₐ[Localization.Away φ] N :=
      { (Algebra.TensorProduct.includeRight.toRingHom).comp (algebraMap B L) with
        commutes' := fun r ↦ by
          show (1 : K1) ⊗ₜ algebraMap B L (algebraMap _ B r) = _
          rw [← IsScalarTower.algebraMap_apply (Localization.Away φ) B L,
            IsScalarTower.algebraMap_apply (Localization.Away φ) K L,
            Algebra.TensorProduct.algebraMap_apply, hK1R]
          exact (Algebra.TensorProduct.algebraMap_apply' (R := K) (A := K1) _).symm.trans
            (Algebra.TensorProduct.algebraMap_apply (R := K) (A := K1) _) }
    exact (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ ↦ Commute.all _ _)).toRingHom.domain_nontrivial
  -- Purity: the base change has a section over `A'_φ`, so `B` embeds into `K[φ^{1/e}]`.
  obtain ⟨σ'⟩ := nonempty_algHom_of_isUnramifiedInCodimensionOne h0BMA A' g hg0 B' hunr
  let τ : B →+* K1 := χ.comp (σ'.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  have hτ : ∀ a : A, τ (algebraMap _ B (algebraMap A (Localization.Away φ) a)) =
      algebraMap K K1 (algebraMap A K a) := by
    intro a
    show χ (σ' ((1 : Cφ) ⊗ₜ algebraMap _ B (algebraMap A (Localization.Away φ) a))) = _
    rw [← Algebra.TensorProduct.algebraMap_apply',
      IsScalarTower.algebraMap_apply (Localization.Away φ) Cφ B', σ'.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, hχR]
    rfl
  -- `B` is a normal domain, integral over `A_φ`.
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  have hBnorm : IsNormalRing B := IsNormalRing.of_etale (isNormalRing_localization_away hφ0)
  have : IsIntegrallyClosed B :=
    IsIntegrallyClosed.of_localization_maximal fun P _ _ ↦ (hBnorm P).2
  -- The identification of `B`, and the exponent is a unit.
  obtain ⟨d, hd0, hde, σ, hσ⟩ := exists_ringEquiv_of_ringHom_K1 (A := A) (A₀ := O) (K := K)
    hπirr he2 (ringChar_eq_zero_or_coprime_of_isUnit hue)
    (fun d hd ↦ have := hreg' d hd; IsRegularLocalRing.isDomain _)
    (fun d hd ↦ have := hreg' d hd; isIntegrallyClosed_of_isRegularLocalRing _)
    B τ hτ
  have : NeZero d := ⟨hd0.ne'⟩
  have hdR : IsUnit (d : Localization.Away φ) := by
    let := (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A φ d)) φ).toAlgebra
    let σA : Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ d) φ) ≃ₐ[
        Localization.Away φ] B := { σ with commutes' := hσ }
    exact isUnit_natCast_of_etale A φ d (Algebra.Etale.of_equiv σA.symm)
  exact ⟨d, hd0, isUnit_of_isUnit_algebraMap_away hp hφ0 (by rwa [map_natCast])
    (natCast_notMem_of_dvd_of_isUnit_residueField (O := O) _ hde hue), σ, hσ⟩

end AlgebraicGeometry.Abhyankar
