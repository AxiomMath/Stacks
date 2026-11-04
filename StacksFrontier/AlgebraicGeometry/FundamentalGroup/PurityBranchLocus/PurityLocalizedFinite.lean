module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.PuncturedEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.Permanence
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.UniquePrimeLocalization
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.NoetherNormalization.Basic

/-!
# Purity of the branch locus for a localization of a finite algebra

Let `T → C` be a finite ring map, let `𝔭` be a prime of `T` and let `𝔮` be the *only* prime of
`C` lying over `𝔭`. Then `T_𝔭 → C_𝔮` is again finite, and [Stacks, Tag 0BMA] clause (2) applies
to it: if `T_𝔭` is regular of dimension at least two, `C_𝔮` is normal of the same dimension, and
`Spec C → Spec T` is étale at every prime of `C` strictly below `𝔮`, then `T_𝔭 → C_𝔮` is étale, so
`C_𝔮` is regular, hence Cohen–Macaulay.

This is the step by which the reduction of [Stacks, Tag 0BMB] to [Stacks, Tag 0BMA] crosses from
a *finite* algebra to the *local ring* of one: the local ring `𝒪_{X,x}` at a point at which a
morphism is quasi-finite is, after an étale base change on the target, the local ring of a finite
algebra at the unique point of a fibre, and never a finite algebra itself.

Tag 0BMA clause (2) is not available in this library beyond dimension two — its inductive step is
[Stacks, Tag 0BLM], which rests on [Stacks, Tag 0BLS] — so it enters here as the explicit
hypothesis `PurityFiniteNormal`, stated in exactly the form
`Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_ringKrullDim_eq_two` proves it for `d = 2`.

## Main definitions

* `Stacks.PurityBranchLocus.PurityFiniteNormal` — [Stacks, Tag 0BMA] clause (2) in every
  dimension `d ≥ 2`, as a proposition.

## Main results

* `Stacks.PurityBranchLocus.isRegularLocalRing_of_purityFiniteNormal` — regularity of `C_𝔮` in
  the situation above, for arbitrary localization models.
* `Stacks.PurityBranchLocus.isCohenMacaulayLocalRing_of_purityFiniteNormal` — the same conclusion
  read as Cohen–Macaulayness, which is the form the étale-local reduction of
  [Stacks, Tag 0BMB] consumes.
* `Stacks.PurityBranchLocus.isRegularLocalRing_localization_of_purityFiniteNormal` — the same for
  the canonical models `Localization.AtPrime 𝔭` and `Localization.AtPrime 𝔮`.
* `Stacks.PurityBranchLocus.injective_algebraMap_of_finite_of_ringKrullDim_eq`,
  `Stacks.PurityBranchLocus.eq_maximalIdeal_of_under_eq`,
  `Stacks.PurityBranchLocus.module_finite_of_isLocalization` and
  `Stacks.PurityBranchLocus.isEtaleAt_of_isEtaleAt_of_isLocalization` — the four steps.

## What is *not* proved here

[Stacks, Tag 0BMB] in dimension at least three. Three things separate the results below from it,
and none of them is claimed anywhere in this file.

* Tag 0BMA clause (2) beyond dimension two, which is the hypothesis `PurityFiniteNormal`. The
  library has that clause only for `d = 2`, as
  `Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_ringKrullDim_eq_two`; the source's
  induction on `d` passes through [Stacks, Tag 0BLM] and hence [Stacks, Tag 0BLS], which this
  library carries only for an `f`-adically complete ring with three further general hypotheses
  granted.
* The passage from a quasi-finite morphism of schemes to the finite situation treated here. The
  source works étale locally on the base ([Stacks, Tags 02VN, 036W]) and makes the morphism
  finite near the point by [Stacks, Tag 02LK], whose carrier in this library is
  `Stacks.Flatness.exists_etaleNeighborhood_finiteAt`; the resulting local rings are compared
  with the original ones by the permanence lemmas [Stacks, Tags 025N, 025P, 025Q, 039S, 0AH0].
  That comparison is not carried out here.
* The induction on `d` which turns the tag's hypothesis on one-dimensional generizations into
  étaleness at *every* generization, i.e. into the hypothesis `haway` below.

## Implementation notes

Both localizations are taken as abstract models: `A` is any `IsLocalization.AtPrime` of `T` at
`𝔭` and `B` any `IsLocalization.AtPrime` of `C` at `𝔮`, so that a stalk of a scheme can be used
directly. That `B` is at the same time the localization of `C` at the image of `T ∖ 𝔭` — which is
what makes it an `A`-algebra and the square a pushout, hence what transports the étale locus by
[Stacks, Tag 00U2] (5) (`Algebra.etaleLocus_eq_of_isPushout`) — is the uniqueness of the prime
over `𝔭`, through `isLocalization_atPrime_of_primesOver_eq_singleton`.

Torsion-freeness of `C_𝔮` over `T_𝔭` is an extra hypothesis of the library's form of
Tag 0BMA clause (2), and is discharged here: `C_𝔮` is a domain, being normal and local, and
`T_𝔭 → C_𝔮` is injective because a nonzero kernel would be a nonzero prime `P` of the domain
`T_𝔭`, forcing `dim (T_𝔭 ⧸ P) < dim T_𝔭`, while `T_𝔭 ⧸ P → C_𝔮` is an injective integral
extension and so `dim (T_𝔭 ⧸ P) = dim C_𝔮 = dim T_𝔭`.

## References

* [Stacks Project, Tag 0BMA](https://stacks.math.columbia.edu/tag/0BMA)
* [Stacks Project, Tag 0BMB](https://stacks.math.columbia.edu/tag/0BMB)
* [Stacks Project, Tag 00U2](https://stacks.math.columbia.edu/tag/00U2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.PurityBranchLocus

/-- **[Stacks, Tag 0BMA] clause (2) in every dimension `d ≥ 2`**, as a proposition: a finite
algebra `B` over a regular local ring `A` of dimension at least two which is a normal ring and
torsion-free over `A`, and whose spectrum is étale over the punctured spectrum of `A`, is étale
over `A`.

This is the statement of `Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_ringKrullDim_eq_two`
with its `ringKrullDim A = 2` relaxed to `2 ≤ ringKrullDim A`; the hypothesis
`Module.IsTorsionFree A B` is the one that lemma documents as necessary and absent from the
source. -/
public def PurityFiniteNormal : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsRegularLocalRing A]
    [Module.Finite A B] [Module.IsTorsionFree A B], IsNormalRing B →
    (2 : WithBot ℕ∞) ≤ ringKrullDim A →
    AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_
      Stacks.puncturedSpectrum A) →
    Algebra.Etale A B

/-! ### Injectivity from equality of dimensions -/

/-- A finite algebra over a Noetherian local domain which is itself a domain of the same Krull
dimension has injective structure map. -/
public lemma injective_algebraMap_of_finite_of_ringKrullDim_eq {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [IsDomain B] (hdim : ringKrullDim B = ringKrullDim A) :
    Function.Injective (algebraMap A B) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hker : (RingHom.ker (algebraMap A B)).IsPrime := RingHom.ker_isPrime _
  -- The kernel is a nonzero prime of the domain `A`, so it sits strictly above `⊥`.
  have hlt : (⊥ : PrimeSpectrum A) < ⟨RingHom.ker (algebraMap A B), hker⟩ :=
    lt_of_le_of_ne bot_le fun h => hne (congrArg PrimeSpectrum.asIdeal h).symm
  have hco := Order.coheight_add_one_le hlt
  -- The quotient by the kernel is an injective integral extension of `B`.
  have hquot : ringKrullDim (A ⧸ RingHom.ker (algebraMap A B)) = ringKrullDim B := by
    refine ringKrullDim_eq_of_injective_isIntegral
      (Ideal.Quotient.lift _ (algebraMap A B)
        fun a ha => RingHom.mem_ker.mp ha) ?_ fun b => ?_
    · rw [RingHom.injective_iff_ker_eq_bot]
      refine le_antisymm (fun z hz => ?_) bot_le
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact (Submodule.Quotient.mk_eq_zero _).mpr hz
    · obtain ⟨p, hmonic, hp⟩ :=
        ((RingHom.finite_algebraMap.mpr ‹Module.Finite A B›).to_isIntegral) b
      refine ⟨p.map (Ideal.Quotient.mk _), hmonic.map _, ?_⟩
      rwa [Polynomial.eval₂_map, Ideal.Quotient.lift_comp_mk]
  have hcoq : (Order.coheight (⟨RingHom.ker (algebraMap A B), hker⟩ : PrimeSpectrum A) :
      WithBot ℕ∞) = ringKrullDim A := by
    rw [coheight_eq_ringKrullDim_quotient, hquot, hdim]
  -- Hence the coheight of the kernel is infinite, so `A` has infinite dimension.
  have hba : Order.coheight (⊥ : PrimeSpectrum A) ≤
      Order.coheight (⟨RingHom.ker (algebraMap A B), hker⟩ : PrimeSpectrum A) := by
    rw [← WithBot.coe_le_coe, hcoq]
    exact Order.coheight_le_krullDim _
  have htop : Order.coheight (⟨RingHom.ker (algebraMap A B), hker⟩ : PrimeSpectrum A) = ⊤ := by
    by_contra h
    exact lt_irrefl _ ((ENat.add_one_le_iff h).mp (hco.trans hba))
  rw [htop] at hcoq
  exact ringKrullDim_ne_top hcoq.symm

/-! ### Primes of a localization at a prime -/

/-- A prime of a localization at `𝔭` whose contraction is `𝔭` is the maximal ideal: a prime of a
localization is the extension of its contraction. -/
public lemma eq_maximalIdeal_of_under_eq {T A : Type u} [CommRing T] [CommRing A] [Algebra T A]
    [IsLocalRing A] (𝔭 : Ideal T) [𝔭.IsPrime] [IsLocalization.AtPrime A 𝔭]
    (P : Ideal A) (h : Ideal.under T P = 𝔭) :
    P = IsLocalRing.maximalIdeal A := by
  calc P = Ideal.map (algebraMap T A) (Ideal.under T P) :=
        (IsLocalization.map_under 𝔭.primeCompl A P).symm
    _ = Ideal.map (algebraMap T A) (Ideal.under T (IsLocalRing.maximalIdeal A)) := by
        rw [h, IsLocalization.AtPrime.under_maximalIdeal A 𝔭]
    _ = IsLocalRing.maximalIdeal A := IsLocalization.map_under 𝔭.primeCompl A _

/-! ### The base change of a finite algebra to the localization of its base -/

/-- The structure map of the base change of `C` to the localization of `T` at `𝔭` is the
localization of `T → C`: both make the localization square commute. -/
public lemma algebraMap_eq_isLocalization_map {T C A B : Type u} [CommRing T] [CommRing C]
    [CommRing A] [CommRing B] [Algebra T C] [Algebra T A] [Algebra C B] [Algebra T B]
    [Algebra A B] [IsScalarTower T C B] [IsScalarTower T A B]
    (𝔭 : Ideal T) [𝔭.IsPrime] [IsLocalization.AtPrime A 𝔭]
    [IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) B] :
    algebraMap A B =
      IsLocalization.map B (algebraMap T C)
        (show 𝔭.primeCompl ≤ Submonoid.comap (algebraMap T C)
          (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) from
          Submonoid.le_comap_map 𝔭.primeCompl) := by
  refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
  rw [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq T A B,
    ← IsScalarTower.algebraMap_eq T C B]

/-- The base change of a finite algebra to the localization of its base is finite. -/
public lemma module_finite_of_isLocalization {T C A B : Type u} [CommRing T] [CommRing C]
    [CommRing A] [CommRing B] [Algebra T C] [Module.Finite T C] [Algebra T A] [Algebra C B]
    [Algebra T B] [Algebra A B] [IsScalarTower T C B] [IsScalarTower T A B]
    (𝔭 : Ideal T) [𝔭.IsPrime] [IsLocalization.AtPrime A 𝔭]
    [IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) B] :
    Module.Finite A B := by
  have _ : IsLocalization (Submonoid.map (algebraMap T C) 𝔭.primeCompl) B :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) B)
  refine RingHom.finite_algebraMap.mp ?_
  rw [algebraMap_eq_isLocalization_map (T := T) (C := C) (A := A) (B := B) 𝔭]
  exact RingHom.finite_localizationPreserves (algebraMap T C) 𝔭.primeCompl A B
    (RingHom.finite_algebraMap.mpr inferInstance)

/-- Étaleness at a prime of `C` is inherited by the corresponding prime of the base change of
`C` to the localization of `T` at `𝔭`. This is [Stacks, Tag 00U2] (5) for the flat base change
`T → T_𝔭`. -/
public lemma isEtaleAt_of_isEtaleAt_of_isLocalization {T C A B : Type u} [CommRing T]
    [CommRing C] [CommRing A] [CommRing B] [Algebra T C] [Algebra T A] [Algebra C B]
    [Algebra T B] [Algebra A B] [IsScalarTower T C B] [IsScalarTower T A B]
    (𝔭 : Ideal T) [𝔭.IsPrime] [IsLocalization.AtPrime A 𝔭]
    [IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) B]
    (Q : Ideal B) [hQ : Q.IsPrime]
    (h : Algebra.IsEtaleAt T (Ideal.under C Q)) :
    Algebra.IsEtaleAt A Q := by
  have _ : Algebra.IsPushout T C A B :=
    Algebra.isPushout_of_isLocalization 𝔭.primeCompl A C B
  have _ : Module.Flat T A := IsLocalization.flat A 𝔭.primeCompl
  have hmem : (⟨Q, hQ⟩ : PrimeSpectrum B) ∈ Algebra.etaleLocus A B := by
    rwa [Algebra.etaleLocus_eq_of_isPushout T C A B]
  exact hmem

/-! ### Purity at the unique prime over a prime of the base -/

/-- **Purity of the branch locus for the localization of a finite algebra.** Let `T → C` be a
finite ring map, let `𝔭` be a prime of `T` and let `𝔮` be the only prime of `C` lying over `𝔭`.
Let `A` be a localization of `T` at `𝔭` and let `B` be a localization of `C` at `𝔮`, compatibly.
Assume `A` is regular of dimension at least two, `B` is a normal ring of the same dimension, and
`Spec C ⟶ Spec T` is étale at every prime of `C` strictly below `𝔮`. Then `B` is regular.

Granting [Stacks, Tag 0BMA] clause (2) in the shape `PurityFiniteNormal`, this is the form of
that tag which applies to the local ring of a finite algebra at the unique point of a fibre, and
hence to the local ring of a scheme at a point at which a morphism is quasi-finite. -/
public theorem isRegularLocalRing_of_purityFiniteNormal (hPurity : PurityFiniteNormal.{u})
    {T C A B : Type u} [CommRing T] [CommRing C] [CommRing A] [CommRing B]
    [Algebra T C] [Module.Finite T C] [Algebra T A] [Algebra C B] [Algebra T B] [Algebra A B]
    [IsScalarTower T C B] [IsScalarTower T A B]
    (𝔭 : Ideal T) [𝔭.IsPrime] (𝔮 : Ideal C) [𝔮.IsPrime]
    [IsLocalization.AtPrime A 𝔭] [IsLocalization.AtPrime B 𝔮]
    (huniq : 𝔭.primesOver C = {𝔮})
    (hreg : IsRegularLocalRing A) (hnormal : IsNormalRing B)
    (hdim : ringKrullDim B = ringKrullDim A)
    (hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (haway : ∀ q : Ideal C, ∀ _ : q.IsPrime, q ≤ 𝔮 → q ≠ 𝔮 → Algebra.IsEtaleAt T q) :
    IsRegularLocalRing B := by
  have _ : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B 𝔮
  have _ : 𝔮.LiesOver 𝔭 := (show 𝔮 ∈ 𝔭.primesOver C by rw [huniq]; rfl).2
  -- `B` is also the localization of `C` at the image of `T ∖ 𝔭`.
  have hsub : IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) B := by
    have _ : IsLocalization.AtPrime
        (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)) 𝔮 :=
      isLocalization_atPrime_of_primesOver_eq_singleton huniq _
    exact IsLocalization.isLocalization_of_algEquiv
      (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)
      (IsLocalization.algEquiv 𝔮.primeCompl
        (Localization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl)) B)
  have _ : Module.Finite A B :=
    module_finite_of_isLocalization (T := T) (C := C) (A := A) (B := B) 𝔭
  have _ : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  -- Torsion-freeness of `B` over `A`, from injectivity.
  obtain ⟨_, -⟩ := hnormal.of_isLocalRing
  have _ : IsDomain A := IsRegularLocalRing.isDomain A
  have hinj : Function.Injective (algebraMap A B) :=
    injective_algebraMap_of_finite_of_ringKrullDim_eq hdim
  have _ : Module.IsTorsionFree A B := by
    refine Module.IsTorsionFree.comap (algebraMap A B) (fun a ha => ?_) fun a b => ?_
    · refine isRegular_iff_ne_zero.mpr fun hz => ?_
      exact (isRegular_iff_ne_zero.mp ha) (hinj (by simpa using hz))
    · exact (Algebra.smul_def a b).symm
  -- A prime of `B` over `𝔮` contracts to the maximal ideal of `A`.
  have hover : ∀ J : Ideal B, Ideal.under C J = 𝔮 → Ideal.under A J = IsLocalRing.maximalIdeal A :=
    fun J hJ => eq_maximalIdeal_of_under_eq 𝔭 _ <| by
      rw [Ideal.under, Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq T A B,
        IsScalarTower.algebraMap_eq T C B, ← Ideal.comap_comap]
      exact (congrArg _ hJ).trans (𝔮.over_def 𝔭).symm
  -- Étaleness over the punctured spectrum, prime by prime.
  have hPS : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_
      Stacks.puncturedSpectrum A) := by
    refine AlgebraicGeometry.etale_specMap_restrict_puncturedSpectrum_of_isEtaleAt ?_
    intro Q hQ hQne
    have hle : Ideal.under C Q ≤ 𝔮 :=
      (Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime Q)).trans
        (IsLocalization.AtPrime.under_maximalIdeal B 𝔮).le
    refine isEtaleAt_of_isEtaleAt_of_isLocalization 𝔭 Q
      (haway _ inferInstance hle fun hcon => ?_)
    exact hQne (hover Q hcon)
  have _ : Algebra.Etale A B := hPurity A B hnormal hdim2 hPS
  have _ : IsLocalHom (algebraMap A B) := by
    refine ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 5 1).mp ?_
    exact hover _ (IsLocalization.AtPrime.under_maximalIdeal B 𝔮)
  refine (RingHom.isRegularLocalRing_iff_of_isEtaleLocalHom (algebraMap A B) ?_).mp hreg
  exact ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
    RingHom.formallyUnramified_algebraMap.mpr inferInstance,
    RingHom.essFiniteType_algebraMap.mpr inferInstance⟩

/-- The Cohen–Macaulay reading of
`Stacks.PurityBranchLocus.isRegularLocalRing_of_purityFiniteNormal`:
a regular local ring is Cohen–Macaulay. This is the shape in which the étale-local reduction of
[Stacks, Tag 0BMB] uses the conclusion: the engine
`etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_isMaximalCohenMacaulay`, in
`AlgebraicGeometry`, asks for Cohen–Macaulayness of the local ring at the point. -/
public theorem isCohenMacaulayLocalRing_of_purityFiniteNormal (hPurity : PurityFiniteNormal.{u})
    {T C A B : Type u} [CommRing T] [CommRing C] [CommRing A] [CommRing B]
    [Algebra T C] [Module.Finite T C] [Algebra T A] [Algebra C B] [Algebra T B] [Algebra A B]
    [IsScalarTower T C B] [IsScalarTower T A B] [IsNoetherianRing B] [IsLocalRing B]
    (𝔭 : Ideal T) [𝔭.IsPrime] (𝔮 : Ideal C) [𝔮.IsPrime]
    [IsLocalization.AtPrime A 𝔭] [IsLocalization.AtPrime B 𝔮]
    (huniq : 𝔭.primesOver C = {𝔮})
    (hreg : IsRegularLocalRing A) (hnormal : IsNormalRing B)
    (hdim : ringKrullDim B = ringKrullDim A)
    (hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (haway : ∀ q : Ideal C, ∀ _ : q.IsPrime, q ≤ 𝔮 → q ≠ 𝔮 → Algebra.IsEtaleAt T q) :
    IsCohenMacaulayLocalRing B :=
  let : IsRegularLocalRing B :=
    isRegularLocalRing_of_purityFiniteNormal hPurity 𝔭 𝔮 huniq hreg hnormal hdim hdim2 haway
  IsRegularLocalRing.isCohenMacaulayLocalRing B

/-- `Stacks.PurityBranchLocus.isRegularLocalRing_of_purityFiniteNormal` for the canonical
localizations `T_𝔭` and `C_𝔮`. -/
public theorem isRegularLocalRing_localization_of_purityFiniteNormal
    (hPurity : PurityFiniteNormal.{u})
    {T C : Type u} [CommRing T] [CommRing C] [Algebra T C] [Module.Finite T C]
    (𝔭 : Ideal T) [𝔭.IsPrime] (𝔮 : Ideal C) [𝔮.IsPrime] [𝔮.LiesOver 𝔭]
    (huniq : 𝔭.primesOver C = {𝔮})
    (hreg : IsRegularLocalRing (Localization.AtPrime 𝔭))
    (hnormal : IsNormalRing (Localization.AtPrime 𝔮))
    (hdim : ringKrullDim (Localization.AtPrime 𝔮) = ringKrullDim (Localization.AtPrime 𝔭))
    (hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime 𝔭))
    (haway : ∀ q : Ideal C, ∀ _ : q.IsPrime, q ≤ 𝔮 → q ≠ 𝔮 → Algebra.IsEtaleAt T q) :
    IsRegularLocalRing (Localization.AtPrime 𝔮) :=
  let := Localization.AtPrime.algebraOfLiesOver 𝔭 𝔮
  isRegularLocalRing_of_purityFiniteNormal hPurity 𝔭 𝔮 huniq hreg hnormal hdim hdim2 haway

end Stacks.PurityBranchLocus

end
