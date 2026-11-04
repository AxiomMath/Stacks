module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.BelowDepth
public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.LocalCohomology.SupportInjectivity.Basic

/-!
# Collapsing the support of local cohomology under a depth bound

Let `I` and `J` be ideals of a Noetherian ring `A` with a dualizing complex, let `M` be a finite
`A`-module, and let `T = associatedSubset I J` be the set of primes `𝔭` with
`V(𝔭) ∩ V(I) ⊆ V(J) ∩ V(I)`. Stacks 0EFI selects from `J` a smaller ideal `J₀` with
`V(J₀) ∩ V(I) = V(J) ∩ V(I)`. Stacks 0EFK adds to the hypotheses of that lemma the condition

(6) `depth_{A_𝔭}(M_𝔭) > s` for every `𝔭 ∈ T` outside `V(I)`,

and concludes that `H^i_{J₀}(M) = H^i_J(M) = H^i_{J+I}(M)` for `i ≤ s`, and that these modules
are annihilated by a power of `I`.

## Main definitions

* `Stacks.Algebraization.DepthGtOnAssociatedSubset` — hypothesis (6).

## Main results

* `Stacks.Algebraization.isZero_localCohomologyModule_atPrime_of_lt_depth` —
  `H^i_{𝔭A_𝔭}(M_𝔭) = 0` below the depth of `M_𝔭`.
* `Stacks.Algebraization.isIso_homologyMap_localCohomologyComparison_stabilizingIdeal` and
  `Stacks.Algebraization.isIso_homologyMap_localCohomologyComparison_sup` — the two
  comparison isomorphisms `H^i_{J+I}(M) ≅ H^i_J(M) ≅ H^i_{J₀}(M)` in degrees `i ≤ s`.
* `Stacks.Algebraization.exists_pow_le_annihilator_localCohomologyModule_sup` and
  `Stacks.Algebraization.exists_pow_le_annihilator_localCohomologyModule_stabilizingIdeal` —
  one power of `I` annihilates those modules in all degrees `i ≤ s`.

## Implementation notes

The two comparison isomorphisms come from the criterion of Stacks 0DWV: a prime `𝔭` in
`V(J₀) \ V(J)` or in `V(J) \ V(J+I)` lies in `T` and avoids `V(I)`, so hypothesis (6) and the
depth-vanishing half of Stacks 0AVZ kill `H^i_{𝔭A_𝔭}(M_𝔭)` for `i ≤ s`. Only the two
unconditional clauses of Stacks 0EFI — that `J₀ ⊆ J` and that `V(J₀) ∩ V(I) = V(J) ∩ V(I)` —
enter, so neither isomorphism depends on the cohomological content of that lemma.

The annihilation is Faltings' annihilator theorem (Stacks 0EFC) applied to the closed subsets
`V(J+I) ⊆ V(I)`: for `𝔭 ∉ V(I)` and `𝔮 ∈ V(J) ∩ V(I)` with `𝔭 ⊆ 𝔮` one has
`depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > s`, by (6) when `𝔭 ∈ T` and by hypothesis (4) of Stacks 0EFI
otherwise; in the latter case `dim((A/𝔭)_𝔮) ≥ 1`, because `𝔭 ⊊ 𝔮` forces the image of `𝔮` in
`A/𝔭` to have positive height. The two annihilation statements carry the extra hypotheses
`0 ≤ s`, which Stacks 0EFC assumes, and `0 ≤ d`, which the source uses silently when it reads
`depth + dim > d + s` as `depth + dim > s`.

Depth is measured in `ℕ∞` and relative dimension in `WithBot ℕ∞`; both are compared with the
integer bounds inside `EInt`, through `Stacks.Algebraization.enatToEInt` and
`Stacks.Algebraization.krullDimToEInt`, exactly as in the statement of Stacks 0EFI.

## References

* [Stacks Project, Tag 0EFK](https://stacks.math.columbia.edu/tag/0EFK)
* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0DWV](https://stacks.math.columbia.edu/tag/0DWV)
* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)

## Tags

local cohomology, depth, annihilator, algebraization
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- If `n < e` in `EInt` for a natural number `n` and `e : ℕ∞`, then `n + 1 ≤ e`. -/
private theorem succ_le_of_intCast_lt_enatToEInt {e : ℕ∞} {n : ℕ}
    (h : ((n : ℤ) : EInt) < enatToEInt e) : ((n + 1 : ℕ) : ℕ∞) ≤ e := by
  cases e with
  | top => exact le_top
  | coe k =>
    have hk : ((n : ℤ) : EInt) < ((k : ℤ) : EInt) := by
      simpa [enatToEInt] using h
    have hnk : (n : ℤ) < (k : ℤ) := WithBotTop.coe_lt_coe.mp hk
    exact_mod_cast (show n + 1 ≤ k by omega)

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **Local cohomology at a prime vanishes below the depth.** For a finite `A`-module `M` and a
prime `𝔭`, the module `H^i_{𝔭A_𝔭}(M_𝔭)` is zero in every degree `i` below
`depth_{A_𝔭}(M_𝔭)`. -/
public theorem isZero_localCohomologyModule_atPrime_of_lt_depth
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : Ideal A) [p.IsPrime] (i : ℤ)
    (hi : (i : EInt) < enatToEInt (Module.depth (Localization.AtPrime p)
      (maximalIdeal (Localization.AtPrime p)) (LocalizedModule p.primeCompl M))) :
    IsZero (localCohomologyModule (Localization.AtPrime p)
      (p.map (algebraMap A (Localization.AtPrime p)))
      ((Ideal.fg_of_isNoetherianRing p).map (algebraMap A (Localization.AtPrime p)))
      (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) i) := by
  rcases lt_or_ge i 0 with hneg | hnonneg
  · exact isZero_localCohomologyModule_of_neg _ _ _ _ i hneg
  by_cases hsub : Subsingleton (LocalizedModule p.primeCompl M)
  · have hz : IsZero (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) :=
      ModuleCat.isZero_iff_subsingleton.mpr hsub
    have hw : IsZero (localCohomologyWithSupportIn (Localization.AtPrime p)
        (PrimeSpectrum.zeroLocus ((p.map (algebraMap A (Localization.AtPrime p)) :
          Ideal (Localization.AtPrime p)) : Set (Localization.AtPrime p)))
        ((DerivedCategory.singleFunctor
          (ModuleCat.{u} (Localization.AtPrime p)) 0).obj
            (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M))) i) :=
      Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ hz))
    exact hw.of_iso (localCohomologyWithSupportInIsoLocalCohomologyModule _ _ _ _ i).symm
  · have hnt : Nontrivial (LocalizedModule p.primeCompl M) :=
      not_subsingleton_iff_nontrivial.mp hsub
    have hIM : maximalIdeal (Localization.AtPrime p) •
        (⊤ : Submodule (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) ≠ ⊤ := by
      intro h
      have htop : (⊤ : Submodule (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top h.ge
          (by simpa using
            (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (Localization.AtPrime p))
              bot_ne_top).ge)
      exact absurd htop (by simp)
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hnonneg).symm⟩
    have hdepth : ((n + 1 : ℕ) : ℕ∞) ≤
        Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl M) :=
      succ_le_of_intCast_lt_enatToEInt hi
    have hz := isZero_localCohomology_of_lt_depth.{u, u}
      (A := Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
      (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) hIM
      (n + 1) hdepth (n : ℤ) (by exact_mod_cast Nat.lt_succ_self n)
    suffices h : ∀ (I : Ideal (Localization.AtPrime p)) (hI : I.FG),
        I = maximalIdeal (Localization.AtPrime p) →
        IsZero (localCohomologyModule (Localization.AtPrime p) I hI
          (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) (n : ℤ)) from
      h _ _ (Localization.AtPrime.map_eq_maximalIdeal (I := p))
    rintro I hI rfl
    exact hz.of_iso (localCohomologyWithSupportInIsoLocalCohomologyModule
      (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p)) hI _ (n : ℤ)).symm

/-- The extended integer attached to an integer is not `⊤`. -/
private theorem intCast_lt_top (s : ℤ) : ((s : ℤ) : EInt) < ⊤ := by
  show (WithBot.some (WithTop.some s)) < (WithBot.some (⊤ : WithTop ℤ))
  exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)

/-- In `EInt`, `depth + dim > s` whenever the depth is above `s` and the dimension is not `⊥`,
or the depth is at least `s` and the dimension is at least `1`. -/
private theorem lt_enatToEInt_add_krullDimToEInt {dep : ℕ∞} {dm : WithBot ℕ∞} {s : ℤ}
    (hcase : ((s : EInt) < enatToEInt dep ∧ dm ≠ ⊥) ∨
      ((s : EInt) ≤ enatToEInt dep ∧ (1 : WithBot ℕ∞) ≤ dm)) :
    enatToEInt dep + krullDimToEInt dm > (s : EInt) := by
  cases dm with
  | bot =>
    rcases hcase with ⟨_, hne⟩ | ⟨_, hle⟩
    · exact (hne rfl).elim
    · exact absurd hle (by simp)
  | coe m =>
    cases m with
    | top => cases dep <;> exact intCast_lt_top s
    | coe b =>
      cases dep with
      | top => exact intCast_lt_top s
      | coe a =>
        have hsum : enatToEInt ((a : ℕ) : ℕ∞) + krullDimToEInt (((b : ℕ) : ℕ∞) : WithBot ℕ∞) =
            (((a + b : ℕ) : ℤ) : EInt) := by
          show ((a : ℤ) : EInt) + ((b : ℤ) : EInt) = _
          push_cast
          rfl
        rw [hsum]
        refine WithBotTop.coe_lt_coe.2 ?_
        rcases hcase with ⟨hlt, -⟩ | ⟨hle, hone⟩
        · have : (s : ℤ) < (a : ℤ) := WithBotTop.coe_lt_coe.1 hlt
          push_cast
          omega
        · have hsa : (s : ℤ) ≤ (a : ℤ) := WithBotTop.coe_le_coe.1 hle
          have hb : 1 ≤ b := by
            exact_mod_cast (WithBot.coe_le_coe.1 hone : ((1 : ℕ) : ℕ∞) ≤ ((b : ℕ) : ℕ∞))
          push_cast
          omega

variable {M : Type u} [AddCommGroup M] [Module A M]

/-- Hypothesis (6) of Stacks 0EFK: a prime outside `V(I)` which lies in
`T = associatedSubset I J` has `depth_{A_𝔭}(M_𝔭) > s`. -/
public def DepthGtOnAssociatedSubset (I J : Ideal A) (s : ℤ) : Prop :=
  ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
    p ∈ associatedSubset I J →
    (s : EInt) < enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M))

variable [Module.Finite A M]

/-- Under hypothesis (6) of Stacks 0EFK the local cohomology of `M_𝔭` supported at `𝔭A_𝔭`
vanishes in every degree `≤ s`, for every prime `𝔭 ∈ T` outside `V(I)`. -/
private theorem isZero_localCohomologyModule_atPrime_of_depthGt
    {I J : Ideal A} {s : ℤ} (h6 : DepthGtOnAssociatedSubset (M := M) I J s)
    (p : Ideal A) [hp : p.IsPrime] (hpI : ¬ I ≤ p)
    (hpT : (⟨p, hp⟩ : PrimeSpectrum A) ∈ associatedSubset I J)
    (i : ℤ) (hi : i ≤ s) :
    IsZero (localCohomologyModule (Localization.AtPrime p)
      (p.map (algebraMap A (Localization.AtPrime p)))
      ((Ideal.fg_of_isNoetherianRing p).map (algebraMap A (Localization.AtPrime p)))
      (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) i) := by
  refine isZero_localCohomologyModule_atPrime_of_lt_depth M p i
    (lt_of_le_of_lt ?_ (h6 ⟨p, hp⟩ ?_ hpT))
  · exact WithBotTop.coe_le_coe.mpr hi
  · simpa [PrimeSpectrum.mem_zeroLocus] using hpI

omit [IsNoetherianRing A] in
/-- The relative dimension `dim((A/𝔭)_𝔮)` as the height of the image of `𝔮` in `A/𝔭`. -/
private theorem ringKrullDim_localization_quotient_eq_height
    (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) =
      ((q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height : WithBot ℕ∞) := by
  let f : A →+* A ⧸ p.asIdeal := Ideal.Quotient.mk p.asIdeal
  let qbar : Ideal (A ⧸ p.asIdeal) := q.asIdeal.map f
  have : qbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) (qbar.comap f) := by
    simpa only [qbar, f, Ideal.comap_map_mk hpq] using
      (inferInstance : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) q.asIdeal)
  have h := ringKrullDim_quotient_map_ker_eq_height f Ideal.Quotient.mk_surjective
    qbar (Localization.AtPrime q.asIdeal)
  have hker : RingHom.ker f = p.asIdeal := Ideal.mk_ker
  rw [hker] at h
  simpa [qbar, f] using h

omit [IsNoetherianRing A] in
/-- At a strict specialization `𝔭 < 𝔮` the relative dimension `dim((A/𝔭)_𝔮)` is at least one. -/
private theorem one_le_ringKrullDim_localization_quotient
    (p q : PrimeSpectrum A) (hpq : p.asIdeal < q.asIdeal) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
      p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) := by
  rw [ringKrullDim_localization_quotient_eq_height p q hpq.le]
  have hprime : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq.le
  have hone : (1 : ℕ∞) ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
    refine Order.one_le_iff_ne_zero.2 fun h0 ↦ ?_
    have hmin : q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) ∈
        minimalPrimes (A ⧸ p.asIdeal) := Ideal.height_eq_zero_iff.1 h0
    rw [minimalPrimes_eq_minimals] at hmin
    have heq : (⊥ : Ideal (A ⧸ p.asIdeal)) = q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) :=
      le_antisymm bot_le (hmin.2 Ideal.isPrime_bot bot_le)
    have hc : Ideal.comap (Ideal.Quotient.mk p.asIdeal)
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)) = q.asIdeal := Ideal.comap_map_mk hpq.le
    rw [← heq, show Ideal.comap (Ideal.Quotient.mk p.asIdeal) (⊥ : Ideal (A ⧸ p.asIdeal)) =
      RingHom.ker (Ideal.Quotient.mk p.asIdeal) from rfl, Ideal.mk_ker] at hc
    exact hpq.ne hc
  exact_mod_cast hone

/-- If every prime between `K` and `L` (containing `K` but not `L`) lies in `T` outside `V(I)`,
then hypothesis (6) makes the comparison `H^i_L(M) → H^i_K(M)` an isomorphism for `i ≤ s`. -/
private theorem isIso_homologyMap_localCohomologyComparison_of_depthGt
    {I J : Ideal A} {s : ℤ} (h6 : DepthGtOnAssociatedSubset (M := M) I J s) {K L : Ideal A}
    (hKL : K ≤ L)
    (hprime : ∀ (p : Ideal A) (hp : p.IsPrime), K ≤ p → ¬ L ≤ p →
      ¬ I ≤ p ∧ (⟨p, hp⟩ : PrimeSpectrum A) ∈ associatedSubset I J)
    (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyComparison A L K (Ideal.fg_of_isNoetherianRing L)
        (Ideal.fg_of_isNoetherianRing K) hKL
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) := by
  rcases lt_or_ge i 0 with hneg | hi0
  · exact ⟨0, (isZero_localCohomologyModule_of_neg A L (Ideal.fg_of_isNoetherianRing L)
      (ModuleCat.of A M) i hneg).eq_of_src _ _,
      (isZero_localCohomologyModule_of_neg A K (Ideal.fg_of_isNoetherianRing K)
        (ModuleCat.of A M) i hneg).eq_of_tgt _ _⟩
  refine isIso_localCohomologyModuleMapOfLE A K L _ _ hKL (ModuleCat.of A M) i hi0 ?_
  intro p hp hKp hLp
  obtain ⟨hpI, hpT⟩ := hprime p hp hKp hLp
  exact ⟨isZero_localCohomologyModule_atPrime_of_depthGt h6 p hpI hpT i hi,
    isZero_localCohomologyModule_atPrime_of_depthGt h6 p hpI hpT (i - 1) (by omega)⟩

section

variable (I J : Ideal A) (s d : ℤ) (omega : DerivedCategory (ModuleCat.{u} A))
  (H : StabilizationHypotheses (M := M) I J s d omega)

/-- Under hypothesis (6) of Stacks 0EFK the local cohomology of `M` supported in the stabilizing
ideal `J₀` of Stacks 0EFI agrees with the local cohomology supported in `J` in all degrees
`i ≤ s`. -/
@[stacks 0EFK "H^i_{J₀}(M) = H^i_J(M) for i ≤ s"]
public theorem isIso_homologyMap_localCohomologyComparison_stabilizingIdeal
    (h6 : DepthGtOnAssociatedSubset (M := M) I J s) (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyComparison A J (stabilizingIdeal I J s d omega H)
        (Ideal.fg_of_isNoetherianRing J)
        (Ideal.fg_of_isNoetherianRing (stabilizingIdeal I J s d omega H))
        (stabilizingIdeal_le I J s d omega H)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) := by
  refine isIso_homologyMap_localCohomologyComparison_of_depthGt h6
    (stabilizingIdeal_le I J s d omega H) (fun p hp hJ₀p hJp ↦ ⟨?_, ?_⟩) i hi
  · intro hIp
    have hmem : (⟨p, hp⟩ : PrimeSpectrum A) ∈
        PrimeSpectrum.zeroLocus ((stabilizingIdeal I J s d omega H : Ideal A) : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) :=
      ⟨(PrimeSpectrum.mem_zeroLocus _ _).2 (SetLike.coe_subset_coe.2 hJ₀p),
        (PrimeSpectrum.mem_zeroLocus _ _).2 (SetLike.coe_subset_coe.2 hIp)⟩
    rw [zeroLocus_stabilizingIdeal_inter I J s d omega H] at hmem
    exact hJp (SetLike.coe_subset_coe.1 ((PrimeSpectrum.mem_zeroLocus _ _).1 hmem.1))
  · intro x hx
    rw [← zeroLocus_stabilizingIdeal_inter I J s d omega H]
    exact ⟨PrimeSpectrum.zeroLocus_anti_mono_ideal hJ₀p hx.1, hx.2⟩

/-- Under hypothesis (6) of Stacks 0EFK the local cohomology of `M` supported in `J` agrees
with the local cohomology supported in `J + I` in all degrees `i ≤ s`. -/
@[stacks 0EFK "H^i_J(M) = H^i_{J + I}(M) for i ≤ s"]
public theorem isIso_homologyMap_localCohomologyComparison_sup
    (h6 : DepthGtOnAssociatedSubset (M := M) I J s) (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyComparison A (J ⊔ I) J
        (Ideal.fg_of_isNoetherianRing (J ⊔ I)) (Ideal.fg_of_isNoetherianRing J) le_sup_left
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) := by
  refine isIso_homologyMap_localCohomologyComparison_of_depthGt h6 le_sup_left
    (fun p hp hJp hJIp ↦ ⟨fun hIp ↦ hJIp (sup_le hJp hIp), ?_⟩) i hi
  intro x hx
  exact ⟨PrimeSpectrum.zeroLocus_anti_mono_ideal hJp hx.1, hx.2⟩

include H in
/-- Under hypothesis (6) of Stacks 0EFK a single power of `I` annihilates `H^i_{J + I}(M)` in
every degree `i ≤ s`. -/
@[stacks 0EFK "H^i_{J + I}(M) is annihilated by a power of I for i ≤ s"]
public theorem exists_pow_le_annihilator_localCohomologyModule_sup
    (h6 : DepthGtOnAssociatedSubset (M := M) I J s) (hs : 0 ≤ s) (hd : 0 ≤ d) :
    ∃ n : ℕ, ∀ i : ℤ, i ≤ s →
      I ^ n ≤ Module.annihilator A
        (localCohomologyModule A (J ⊔ I) (Ideal.fg_of_isNoetherianRing (J ⊔ I))
          (ModuleCat.of A M) i) := by
  have hTT' : PrimeSpectrum.zeroLocus ((J ⊔ I : Ideal A) : Set A) ⊆
      PrimeSpectrum.zeroLocus (I : Set A) :=
    PrimeSpectrum.zeroLocus_anti_mono_ideal le_sup_right
  have hdepth : ∀ p q : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      q ∈ PrimeSpectrum.zeroLocus ((J ⊔ I : Ideal A) : Set A) →
      p.asIdeal ≤ q.asIdeal →
      enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (s : EInt) := by
    intro p q hp hq hpq
    have hJIq : (J ⊔ I : Ideal A) ≤ q.asIdeal :=
      SetLike.coe_subset_coe.1 ((PrimeSpectrum.mem_zeroLocus _ _).1 hq)
    have hpI : ¬ I ≤ p.asIdeal := by simpa [PrimeSpectrum.mem_zeroLocus] using hp
    have hlt : p.asIdeal < q.asIdeal :=
      lt_of_le_of_ne hpq fun h ↦ hpI (by rw [h]; exact le_sup_right.trans hJIq)
    by_cases hpT : p ∈ associatedSubset I J
    · refine lt_enatToEInt_add_krullDimToEInt (Or.inl ⟨h6 p hp hpT, ?_⟩)
      rw [ringKrullDim_localization_quotient_eq_height p q hpq]
      exact WithBot.coe_ne_bot
    · rcases H.depthOrDimensionBound p hp hpT with hge | hgt
      · exact lt_enatToEInt_add_krullDimToEInt
          (Or.inr ⟨hge, one_le_ringKrullDim_localization_quotient p q hlt⟩)
      · refine lt_of_le_of_lt (WithBotTop.coe_le_coe.2 (by omega)) (hgt q ⟨⟨?_, ?_⟩, ?_⟩)
        · exact (PrimeSpectrum.mem_zeroLocus _ _).2 (SetLike.coe_subset_coe.2 hpq)
        · exact (PrimeSpectrum.mem_zeroLocus _ _).2
            (SetLike.coe_subset_coe.2 (le_sup_left.trans hJIq))
        · exact (PrimeSpectrum.mem_zeroLocus _ _).2
            (SetLike.coe_subset_coe.2 (le_sup_right.trans hJIq))
  obtain ⟨b, hbsub, hbann⟩ :=
    (Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff A M
      (PrimeSpectrum.zeroLocus ((J ⊔ I : Ideal A) : Set A))
      (PrimeSpectrum.zeroLocus (I : Set A)) hTT'
      (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
      (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization s hs omega
      H.dualizing).2 hdepth
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff b I).1 hbsub)
    (Ideal.fg_of_isNoetherianRing I)
  refine ⟨n, fun i hi ↦ le_trans hn (le_trans (hbann i hi) (le_of_eq ?_))⟩
  exact (localCohomologyWithSupportInIsoLocalCohomologyModule A (J ⊔ I)
    (Ideal.fg_of_isNoetherianRing (J ⊔ I)) (ModuleCat.of A M) i).toLinearEquiv.annihilator_eq

/-- Under hypothesis (6) of Stacks 0EFK a single power of `I` annihilates the local cohomology
of `M` supported in the stabilizing ideal `J₀` of Stacks 0EFI, in every degree `i ≤ s`. -/
@[stacks 0EFK "H^i_{J₀}(M) is annihilated by a power of I for i ≤ s"]
public theorem exists_pow_le_annihilator_localCohomologyModule_stabilizingIdeal
    (h6 : DepthGtOnAssociatedSubset (M := M) I J s) (hs : 0 ≤ s) (hd : 0 ≤ d) :
    ∃ n : ℕ, ∀ i : ℤ, i ≤ s →
      I ^ n ≤ Module.annihilator A
        (localCohomologyModule A (stabilizingIdeal I J s d omega H)
          (Ideal.fg_of_isNoetherianRing (stabilizingIdeal I J s d omega H))
          (ModuleCat.of A M) i) := by
  obtain ⟨n, hn⟩ := exists_pow_le_annihilator_localCohomologyModule_sup I J s d omega H h6 hs hd
  refine ⟨n, fun i hi ↦ (hn i hi).trans (le_of_eq ?_)⟩
  have h₁ := isIso_homologyMap_localCohomologyComparison_sup I J s h6 i hi
  have h₂ := isIso_homologyMap_localCohomologyComparison_stabilizingIdeal I J s d omega H h6 i hi
  exact (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (localCohomologyComparison A (J ⊔ I) J (Ideal.fg_of_isNoetherianRing (J ⊔ I))
          (Ideal.fg_of_isNoetherianRing J) le_sup_left
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) ≪≫
      asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (localCohomologyComparison A J (stabilizingIdeal I J s d omega H)
          (Ideal.fg_of_isNoetherianRing J)
          (Ideal.fg_of_isNoetherianRing (stabilizingIdeal I J s d omega H))
          (stabilizingIdeal_le I J s d omega H)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A M))))).toLinearEquiv.annihilator_eq

end

end Stacks.Algebraization

end
