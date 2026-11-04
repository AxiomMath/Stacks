module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSurjective
public import StacksFrontier.RingTheory.Dualizing.MinimalPrimeNonvanishing
public import StacksFrontier.RingTheory.Localization.LocalizedModuleTwoStep
public import StacksFrontier.Topology.Dimension.DimensionFunction

/-!
# The dimension function of a dualizing complex is a dimension function

Let `A` be a Noetherian ring and `K` a dualizing complex over `A`. The function
`δ_K : Spec A → ℤ` of `Dualizing.dualizingDimension` is a dimension function on `Spec A`: it
drops by exactly one along an immediate specialization and drops strictly along every
non-trivial specialization.

The step along an immediate specialization `p ⤳ q` is computed after replacing `A` by `A/p`,
which is legitimate because the dimension function of `RHom_A(A/p, K)` is the restriction of
`δ_K` along `Spec A/p → Spec A`. This reduces the statement to a Noetherian domain `A` with
`p = (0)` and `q` of height one. There the localization `H^i(K)_{(0)}` of the cohomology at the
generic point is nonzero for exactly one `i`, and that `i` can be computed in two ways: from the
normalized complex `K_{(0)}⟦-δ_K((0))⟧` over the zero-dimensional ring `A_{(0)}`, which gives
`i = -δ_K((0))`, and from the normalized complex `K_q⟦-δ_K(q)⟧` over the one-dimensional ring
`A_q`, which gives `i = -1 - δ_K(q)`. Hence `δ_K((0)) = δ_K(q) + 1`.

The strict decrease then follows formally from the step by induction on the gap between the
heights of the two primes, which is finite because `A` is Noetherian.

## Main definitions

* `Dualizing.dualizingDimensionFunction` — the dimension function on `Spec A` attached to a
  dualizing complex, bundled as a `TopologicalSpace.DimensionFunction`.

## Main results

* `Dualizing.dualizingDimension_eq_succ_of_isImmediateSpecialization` — `δ_K` drops by exactly
  one along an immediate specialization.
* `Dualizing.dualizingDimension_lt_of_specializes` — `δ_K` drops strictly along a non-trivial
  specialization.

## References

* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
* [Stacks Project, Tag 0A7Y](https://stacks.math.columbia.edu/tag/0A7Y)
* [Stacks Project, Tag 0A7X](https://stacks.math.columbia.edu/tag/0A7X)
* [Stacks Project, Tag 0A7V](https://stacks.math.columbia.edu/tag/0A7V)
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
-/

@[expose] public noncomputable section

open CategoryTheory StacksDraft.PseudoCoherence TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-! ### Localizing twice

The cohomology of `K` localized at the generic point of a domain can be computed either
directly or after first localizing at a prime `q`. -/

/-- The two ways of localizing at a prime of `A[T⁻¹]`, directly over `A` or in two steps,
agree. -/
private def localizationTwiceEquiv
    {A : Type u} {M : Type (max v u)} [CommRing A]
    [AddCommGroup M] [Module A M] (T : Submonoid A)
    (P : Ideal (Localization T)) [P.IsPrime] :
    let p := P.comap (algebraMap A (Localization T))
    LocalizedModule p.primeCompl M ≃ₗ[A]
      LocalizedModule P.primeCompl (LocalizedModule T M) := by
  let p := P.comap (algebraMap A (Localization T))
  haveI : p.IsPrime := Ideal.comap_isPrime _ P
  haveI : IsLocalization p.primeCompl (Localization.AtPrime P) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime T P
  let g : M →ₗ[A] LocalizedModule P.primeCompl (LocalizedModule T M) :=
    (LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule T M)).restrictScalars A ∘ₗ
      LocalizedModule.mkLinearMap T M
  haveI : IsLocalizedModule p.primeCompl g := Stacks.isLocalizedModule_comp_mkLinearMap T M P
  exact IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M) g

/-- Over a Noetherian domain the cohomology of `K` at the generic point may be computed after
first localizing `K` at any prime `q`: the two localizations are isomorphic, so one is nonzero
exactly when the other is. -/
private theorem nontrivial_generic_homology_localization_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (q : PrimeSpectrum A)
    (i : ℤ) :
    Nontrivial (LocalizedModule (⊥ : Ideal A).primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K)) ↔
    Nontrivial (LocalizedModule (⊥ : Ideal (Localization.AtPrime q.asIdeal)).primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u}
        (Localization.AtPrime q.asIdeal)) i).obj
        ((derivedExtensionScalars (algebraMap A (Localization.AtPrime q.asIdeal))).obj K))) := by
  let T := q.asIdeal.primeCompl
  let R := Localization.AtPrime q.asIdeal
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing T R inferInstance
  let L := (derivedExtensionScalars (algebraMap A R)).obj K
  let M := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj L
  let : Module A N := Module.compHom N (algebraMap A R)
  have : IsScalarTower A R N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let P : Ideal R := ⊥
  have hcomap : P.comap (algebraMap A R) = ⊥ := by
    rw [← Ideal.comap_bot_of_injective (algebraMap A R)
      (IsLocalization.injective R q.asIdeal.primeCompl_le_nonZeroDivisors)]
  have hprimeCompl :
      (P.comap (algebraMap A R)).primeCompl = (⊥ : Ideal A).primeCompl := by
    ext x
    show x ∉ P.comap (algebraMap A R) ↔ x ∉ (⊥ : Ideal A)
    rw [hcomap]
  have eTwice : LocalizedModule (⊥ : Ideal A).primeCompl M ≃ₗ[A]
      LocalizedModule P.primeCompl (LocalizedModule T M) :=
    hprimeCompl.symm ▸ localizationTwiceEquiv (A := A) (M := M) T P
  let U := ModuleCat.uliftFunctor.{u, max v u} A
  let eHom := (mapDerivedCategoryCompHomologyFunctorIso U i).app K
  let eLift := (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max v u} T).mapIso eHom
  let eULift := localizedModuleUliftIso.{u, max v u} (R := A) (S := T)
    (M := ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K))
  let eLoc :=
    (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, max v u}
      T (A := R) i).app (U.mapDerivedCategory.obj K)
  have eLocType : (ModuleCat.restrictScalars (algebraMap A R)).obj N ≅
      ModuleCat.of A (LocalizedModule T M) := by
    show (ModuleCat.restrictScalars (algebraMap A R)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj
        ((derivedExtensionScalars (algebraMap A R)).obj K)) ≅ _
    exact eLoc ≪≫ eLift ≪≫ eULift
  have : IsScalarTower A R ((ModuleCat.restrictScalars (algebraMap A R)).obj N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eLocR : N ≃ₗ[R] LocalizedModule T M :=
    eLocType.toLinearEquiv.extendScalarsOfIsLocalization T R
  let eLocGeneric :=
    (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max v u} P.primeCompl).mapIso
      eLocR.toModuleIso
  let eLocGenericA := (ModuleCat.restrictScalars (algebraMap A R)).mapIso eLocGeneric
  exact (eTwice.toEquiv.trans eLocGenericA.symm.toLinearEquiv.toEquiv).nontrivial_congr

/-! ### Passing to the quotient by the generic point -/

/-- The image in `A/p` of a prime `q` containing `p`. -/
private def quotientPrime {A : Type u} [CommRing A] (p q : PrimeSpectrum A)
    (hpq : p.asIdeal ≤ q.asIdeal) : PrimeSpectrum (A ⧸ p.asIdeal) :=
  ⟨Ideal.map (Ideal.Quotient.mk p.asIdeal) q.asIdeal,
    Ideal.map_isPrime_of_surjective (Ideal.Quotient.mk_surjective (I := p.asIdeal))
      (by rw [Ideal.mk_ker]; exact hpq)⟩

/-- The image of `q` in `A/p` contracts back to `q`. -/
private theorem comap_quotientPrime {A : Type u} [CommRing A] (p q : PrimeSpectrum A)
    (hpq : p.asIdeal ≤ q.asIdeal) :
    PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) (quotientPrime p q hpq) = q := by
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk p.asIdeal)
    (Ideal.map (Ideal.Quotient.mk p.asIdeal) q.asIdeal) = q.asIdeal
  rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk p.asIdeal)
    (Ideal.Quotient.mk_surjective (I := p.asIdeal)) q.asIdeal, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hpq]

/-- The generic point of `Spec A/p` contracts to `p`. -/
private theorem quotientBot_comap {A : Type u} [CommRing A] (p : PrimeSpectrum A)
    [IsDomain (A ⧸ p.asIdeal)] :
    PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal)
      (⊥ : PrimeSpectrum (A ⧸ p.asIdeal)) = p := by
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk p.asIdeal) ⊥ = p.asIdeal
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- An immediate specialization `p ⤳ q` becomes an immediate specialization from the generic
point of `Spec A/p`. -/
private theorem quotient_immediate {A : Type u} [CommRing A] (p q : PrimeSpectrum A)
    (hpq : p.asIdeal ≤ q.asIdeal) (himm : IsImmediateSpecialization p q) :
    letI : IsDomain (A ⧸ p.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).2 p.isPrime
    IsImmediateSpecialization (⊥ : PrimeSpectrum (A ⧸ p.asIdeal))
      (quotientPrime p q hpq) := by
  let : IsDomain (A ⧸ p.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).2 p.isPrime
  let f := Ideal.Quotient.mk p.asIdeal
  let qbar := quotientPrime p q hpq
  have hcq : PrimeSpectrum.comap f qbar = q := comap_quotientPrime p q hpq
  refine (isImmediateSpecialization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · exact (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  · intro h
    have h' := congrArg (PrimeSpectrum.comap f) h
    rw [quotientBot_comap, hcq] at h'
    exact ((isImmediateSpecialization_iff p q).mp himm).2.1 h'
  · intro z hz0 hzq
    let r := PrimeSpectrum.comap f z
    have hrlo : p ≤ r := by
      rw [← quotientBot_comap p]
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
        (Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp bot_le))
    have hrhi : r ≤ q := by
      rw [← hcq]
      apply (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
      exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp
        ((PrimeSpectrum.le_iff_specializes _ _).mpr hzq))
    obtain hEq | hEq := ((isImmediateSpecialization_iff p q).mp himm).2.2 r
        ((PrimeSpectrum.le_iff_specializes _ _).mp hrlo)
        ((PrimeSpectrum.le_iff_specializes _ _).mp hrhi)
    · left
      apply (PrimeSpectrum.comap_injective_of_surjective f
        (Ideal.Quotient.mk_surjective (I := p.asIdeal)))
      show PrimeSpectrum.comap f z = PrimeSpectrum.comap f (⊥ : PrimeSpectrum (A ⧸ p.asIdeal))
      exact hEq.trans (quotientBot_comap p).symm
    · right
      apply (PrimeSpectrum.comap_injective_of_surjective f
        (Ideal.Quotient.mk_surjective (I := p.asIdeal)))
      show PrimeSpectrum.comap f z = PrimeSpectrum.comap f qbar
      exact hEq.trans hcq.symm

/-- A prime of a Noetherian domain that is an immediate specialization of the generic point has
height one. -/
private theorem height_eq_one_of_bot_immediate {B : Type u} [CommRing B]
    [IsNoetherianRing B] [IsDomain B] {q : PrimeSpectrum B}
    (himm : IsImmediateSpecialization (⊥ : PrimeSpectrum B) q) : q.asIdeal.height = 1 := by
  have hparts := (isImmediateSpecialization_iff (⊥ : PrimeSpectrum B) q).mp himm
  have hbotq : (⊥ : PrimeSpectrum B) < q := bot_lt_iff_ne_bot.mpr (Ne.symm hparts.2.1)
  have : q.asIdeal.FiniteHeight := Ideal.finiteHeight_of_isNoetherianRing _
  have hfinite : Order.height q < ⊤ := by
    simpa [PrimeSpectrum.height_eq_orderHeight] using
      (Ideal.height_lt_top_of_isPrime : q.asIdeal.height < ⊤)
  have horder : Order.height q = (1 : ℕ∞) :=
    (Order.height_eq_coe_add_one_iff).2 ⟨hfinite,
      ⟨⊥, hbotq, Order.height_bot _⟩,
      fun y hy => by
        have hyEq := hparts.2.2 y
          ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)
          ((PrimeSpectrum.le_iff_specializes _ _).mp (le_of_lt hy))
        rcases hyEq with rfl | hEq
        · simp
        · subst y
          exact False.elim (lt_irrefl q hy)⟩
  simpa [PrimeSpectrum.height_eq_orderHeight] using horder

/-! ### The step at the generic point of a domain -/

/-- Over a Noetherian domain, at a prime `q` of height `d` the cohomology of `K` at the generic
point is nonzero in degree `-d - δ_K(q)`. -/
private theorem nontrivial_generic_homology_of_height
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (q : PrimeSpectrum A) (d : ℕ) (hq : q.asIdeal.height = d) :
    Nontrivial (LocalizedModule (⊥ : Ideal A).primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A)
        (-(d : ℤ) - dualizingDimension.{u, v} K q)).obj K)) := by
  let R := Localization.AtPrime q.asIdeal
  have : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl R inferInstance
  let Kq := (derivedExtensionScalars (algebraMap A R)).obj K
  let n := dualizingDimension.{u, v} K q
  have hn : IsNormalizedDualizingComplex.{u, v} (Kq⟦-n⟧) :=
    dualizingDimension_spec.{u, v} K hK q
  have hmin : IsMinimalPrime (⊥ : Ideal R) := ⟨⟨inferInstance, bot_le⟩, fun _ _ _ => bot_le⟩
  have hdim : ringKrullDim (R ⧸ (⊥ : Ideal R)) = ((d : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)]
    simpa [hq] using IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal R
  have hloc : Nontrivial (LocalizedModule (⊥ : PrimeSpectrum R).asIdeal.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) (-(d : ℤ))).obj (Kq⟦-n⟧))) :=
    (nontrivial_localized_homology_iff_eq_neg_dimension.{u, v} (Kq⟦-n⟧) hn
      (⊥ : PrimeSpectrum R) hmin d hdim (-(d : ℤ))).mpr rfl
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) 0
  let eShift :=
    (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max v u}
      (⊥ : PrimeSpectrum R).asIdeal.primeCompl).mapIso
        ((H.shiftIso (-n) (-(d : ℤ)) (-(d : ℤ) - n) (by omega)).app Kq)
  have hraw : Nontrivial (LocalizedModule (⊥ : PrimeSpectrum R).asIdeal.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) (-(d : ℤ) - n)).obj Kq)) :=
    eShift.toLinearEquiv.toEquiv.nontrivial_congr.mp hloc
  exact (nontrivial_generic_homology_localization_iff.{u, v} K q (-(d : ℤ) - n)).2 hraw

/-- Over a Noetherian domain the dimension function drops by one from the generic point to a
prime of height one. -/
private theorem dualizingDimension_bot_heightOne_step
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsDualizingComplex K) (q : PrimeSpectrum A)
    (hq : q.asIdeal.height = 1) :
    dualizingDimension.{u, v} K (⊥ : PrimeSpectrum A) =
      dualizingDimension.{u, v} K q + 1 := by
  have hminA : IsMinimalPrime (⊥ : Ideal A) := ⟨⟨inferInstance, bot_le⟩, fun _ _ _ => bot_le⟩
  obtain ⟨i₀, -, hi₀_unique⟩ :=
    existsUnique_nontrivial_localized_homology.{u, max v u} K hK (⊥ : Ideal A) hminA
  have hheight₀ : (⊥ : PrimeSpectrum A).asIdeal.height = ((0 : ℕ) : ℕ∞) :=
    Ideal.height_eq_zero_iff.2 (show (⊥ : Ideal A) ∈ minimalPrimes A from hminA)
  have h₀ := hi₀_unique _ (nontrivial_generic_homology_of_height.{u, v} K hK ⊥ 0 hheight₀)
  have h₁ := hi₀_unique _
    (nontrivial_generic_homology_of_height.{u, v} K hK q 1 (by simpa using hq))
  push_cast at h₀ h₁
  omega

/-! ### The dimension function -/

/-- The dimension function of a dualizing complex drops by exactly one along an immediate
specialization. -/
@[stacks 0A7Z "δ(p) = δ(q) + 1 for an immediate specialization p ⤳ q"]
theorem dualizingDimension_eq_succ_of_isImmediateSpecialization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    {p q : PrimeSpectrum A} (himm : IsImmediateSpecialization p q) :
    dualizingDimension.{u, v} K p = dualizingDimension.{u, v} K q + 1 := by
  have hpq : p.asIdeal ≤ q.asIdeal :=
    (PrimeSpectrum.asIdeal_le_asIdeal p q).mpr
      ((PrimeSpectrum.le_iff_specializes p q).mpr
        ((isImmediateSpecialization_iff p q).mp himm).1)
  let f := Ideal.Quotient.mk p.asIdeal
  have : IsDomain (A ⧸ p.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).2 p.isPrime
  let qbar := quotientPrime p q hpq
  have hheight : qbar.asIdeal.height = 1 :=
    height_eq_one_of_bot_immediate (quotient_immediate p q hpq himm)
  let Kbar := (derivedHom.{u, v} f).obj K
  have hKbar : IsDualizingComplex Kbar :=
    isDualizingComplex_derivedHom_of_finite.{u, v} f
      (RingHom.Finite.of_surjective f (Ideal.Quotient.mk_surjective (I := p.asIdeal))) K hK
  have hdimQ : dualizingDimension.{u, v} Kbar qbar = dualizingDimension.{u, v} K q := by
    have h := dualizingDimension_derivedHom_of_surjective.{u, v} f
      (Ideal.Quotient.mk_surjective (I := p.asIdeal)) K hK qbar
    rwa [comap_quotientPrime p q hpq] at h
  have hdimP : dualizingDimension.{u, v} Kbar (⊥ : PrimeSpectrum (A ⧸ p.asIdeal)) =
      dualizingDimension.{u, v} K p := by
    have h := dualizingDimension_derivedHom_of_surjective.{u, v} f
      (Ideal.Quotient.mk_surjective (I := p.asIdeal)) K hK
      (⊥ : PrimeSpectrum (A ⧸ p.asIdeal))
    rwa [quotientBot_comap p] at h
  rw [← hdimP, ← hdimQ]
  exact dualizingDimension_bot_heightOne_step.{u, v} Kbar hKbar qbar hheight

/-- In a Noetherian ring the height of a prime jumps along a strict inclusion of primes. -/
private theorem height_toNat_lt {A : Type*} [CommRing A] [IsNoetherianRing A]
    {I J : Ideal A} [I.IsPrime] [J.IsPrime] (h : I < J) : I.height.toNat < J.height.toNat := by
  have : I.FiniteHeight := Ideal.finiteHeight_of_isNoetherianRing I
  have : J.FiniteHeight := Ideal.finiteHeight_of_isNoetherianRing J
  have hlt : I.height < J.height := Ideal.height_strict_mono_of_isPrime_of_isPrime h
  have hI : I.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have hJ : J.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have hlt' : (I.height.toNat : ℕ∞) < (J.height.toNat : ℕ∞) := by
    simpa [ENat.natCast_toNat hI, ENat.natCast_toNat hJ] using hlt
  exact_mod_cast hlt'

/-- On the spectrum of a Noetherian ring an integer-valued function that drops by one along
every immediate specialization drops strictly along every non-trivial specialization. -/
private theorem strictAnti_of_step {A : Type*} [CommRing A] [IsNoetherianRing A]
    (d : PrimeSpectrum A → ℤ)
    (hstep : ∀ ⦃p q : PrimeSpectrum A⦄, IsImmediateSpecialization p q → d p = d q + 1) :
    ∀ ⦃p q : PrimeSpectrum A⦄, p ⤳ q → p ≠ q → d q < d p := by
  classical
  have hmain : ∀ n : ℕ, ∀ (p q : PrimeSpectrum A),
      q.asIdeal.height.toNat - p.asIdeal.height.toNat = n → p ⤳ q → p ≠ q → d q < d p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p q _ hpq hne
      have hpq' : p.asIdeal < q.asIdeal :=
        lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes p q).2 hpq)
          fun h => hne (PrimeSpectrum.ext h)
      have hh : p.asIdeal.height.toNat < q.asIdeal.height.toNat := height_toNat_lt hpq'
      by_cases himm : IsImmediateSpecialization p q
      · have h := hstep himm
        omega
      · obtain ⟨r, hpr, hrq, hrp, hrq'⟩ :
            ∃ r : PrimeSpectrum A, p ⤳ r ∧ r ⤳ q ∧ r ≠ p ∧ r ≠ q := by
          by_contra hcon
          refine himm ((isImmediateSpecialization_iff p q).2 ⟨hpq, hne, fun r hpr hrq => ?_⟩)
          by_cases h1 : r = p
          · exact Or.inl h1
          · by_cases h2 : r = q
            · exact Or.inr h2
            · exact absurd ⟨r, hpr, hrq, h1, h2⟩ hcon
        have hppr : p.asIdeal < r.asIdeal :=
          lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes p r).2 hpr)
            fun h => hrp (PrimeSpectrum.ext h.symm)
        have hrq'' : r.asIdeal < q.asIdeal :=
          lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes r q).2 hrq)
            fun h => hrq' (PrimeSpectrum.ext h)
        have hprh : p.asIdeal.height.toNat < r.asIdeal.height.toNat := height_toNat_lt hppr
        have hrqh : r.asIdeal.height.toNat < q.asIdeal.height.toNat := height_toNat_lt hrq''
        have h1 : d r < d p := ih (r.asIdeal.height.toNat - p.asIdeal.height.toNat) (by omega)
          p r (by omega) hpr (Ne.symm hrp)
        have h2 : d q < d r := ih (q.asIdeal.height.toNat - r.asIdeal.height.toNat) (by omega)
          r q (by omega) hrq hrq'
        exact lt_trans h2 h1
  intro p q hpq hne
  exact hmain (q.asIdeal.height.toNat - p.asIdeal.height.toNat) p q rfl hpq hne

/-- The dimension function of a dualizing complex drops strictly along a non-trivial
specialization. -/
@[stacks 0A7Z "δ(q) < δ(p) for a non-trivial specialization p ⤳ q"]
theorem dualizingDimension_lt_of_specializes
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    {p q : PrimeSpectrum A} (hpq : p ⤳ q) (hne : p ≠ q) :
    dualizingDimension.{u, v} K q < dualizingDimension.{u, v} K p :=
  strictAnti_of_step (dualizingDimension.{u, v} K)
    (fun _ _ himm => dualizingDimension_eq_succ_of_isImmediateSpecialization.{u, v} K hK himm)
    hpq hne

/-- The dimension function `δ_K` of a dualizing complex `K` over a Noetherian ring `A`, as a
dimension function on `Spec A`. -/
@[stacks 0A7Z "the function δ of a dualizing complex is a dimension function on Spec A"]
def dualizingDimensionFunction {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K) :
    TopologicalSpace.DimensionFunction (PrimeSpectrum A) where
  toFun := dualizingDimension.{u, v} K
  strictAnti_specializes _ _ hpq hne := dualizingDimension_lt_of_specializes.{u, v} K hK hpq hne
  step_immediate _ _ himm :=
    dualizingDimension_eq_succ_of_isImmediateSpecialization.{u, v} K hK himm

/-- The dimension function `dualizingDimensionFunction K hK` takes the value
`dualizingDimension K p` at a prime `p`. -/
@[simp]
theorem dualizingDimensionFunction_apply {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) :
    dualizingDimensionFunction.{u, v} K hK p = dualizingDimension.{u, v} K p :=
  rfl

/-- The dimension function on `Spec A` attached to a dualizing complex whose modules live in an
arbitrary universe, read off the complex transported along the identity. -/
def dualizingDimensionFunctionOfArbitraryUniverse
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K) :
    TopologicalSpace.DimensionFunction (PrimeSpectrum A) :=
  dualizingDimensionFunction.{u, v} ((derivedExtensionScalars (algebraMap A A)).obj K)
    (isDualizingComplex_derivedExtensionScalars_self.{u, v} K hK)

end Dualizing

end
