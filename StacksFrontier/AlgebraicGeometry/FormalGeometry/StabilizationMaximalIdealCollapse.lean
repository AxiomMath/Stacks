module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationDepthCollapse
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal
import StacksFrontier.RingTheory.Jacobson.Criteria

/-!
# Collapsing local cohomology onto the maximal ideal under a depth bound

Let `(A, 𝔪)` be a Noetherian local ring, let `I ⊂ A` be an ideal, let `M` be a finite
`A`-module and fix integers `s` and `d`. Stacks 0DXM produces, under hypotheses (1)–(4)
recorded in `Stacks.Algebraization.LocalStabilizationHypotheses`, an ideal `J₀` with
`V(J₀) ∩ V(I) = {𝔪}` that computes the local cohomology of `M` in degrees `≤ s` for every
further ideal `J ⊆ J₀` with `V(J) ∩ V(I) = {𝔪}`. Stacks 0EFQ adds to those hypotheses

(6) if `𝔭 ∉ V(I)` and `V(𝔭) ∩ V(I) = {𝔪}`, then `depth_{A_𝔭}(M_𝔭) > s`,

and concludes that `H^i_{J₀}(M) = H^i_J(M) = H^i_𝔪(M)` for `i ≤ s`, and that these modules are
annihilated by a power of `I`.

## Main definitions

* `Stacks.Algebraization.DepthGtAtMaximalIdeal` — hypothesis (6) of Stacks 0EFQ.

## Main results

* `Stacks.Algebraization.depthGtOnAssociatedSubset_maximalIdeal_iff` — hypothesis (6) of
  Stacks 0EFQ is hypothesis (6) of Stacks 0EFK at `J = 𝔪`.
* `Stacks.Algebraization.isIso_homologyMap_localCohomologyComparison_of_zeroLocus_inter` — the
  comparison `RΓ_L(M) → RΓ_K(M)` is an isomorphism in degrees `≤ s` whenever `K ≤ L ≤ 𝔪` and
  `V(K) ∩ V(I) = {𝔪}`.
* `Stacks.Algebraization.isIso_homologyMap_localCohomologyComparison_maximalIdeal`,
  `Stacks.Algebraization.isIso_homologyMap_localCohomologyComparison_stabilizingIdeal_maximalIdeal`
  and
  `Stacks.Algebraization.isIso_homologyMap_localCohomologyComparison_stabilizingIdeal_of_depthGt`
  — the chain `H^i_{J₀}(M) = H^i_J(M) = H^i_𝔪(M)` in degrees `i ≤ s`.
* `Stacks.Algebraization.exists_pow_le_annihilator_localCohomologyModule_maximalIdeal_of_depthGt`
  — one power of `I` annihilates `H^i_J(M)` for `i ≤ s`, uniformly in `i` and in every ideal `J`
  with `V(J) ∩ V(I) = {𝔪}`, in particular for `J = 𝔪` and `J = J₀`.
* `Stacks.Algebraization.exists_pow_le_annihilator_localCohomologyModule_maximalIdeal` — the same
  statement under the two additional hypotheses `0 ≤ s` and `0 ≤ d`.

## Implementation notes

The direction of the comparison is `RΓ_L(M) → RΓ_K(M)` for `K ≤ L`, as in
`Stacks.Algebraization.localCohomologyComparison`: sections supported in the smaller closed set
`V(L)` are sections supported in `V(K)`, and there is no canonical map the other way. Each
equality of local cohomology modules is stated as the assertion that this canonical arrow is an
isomorphism on cohomology.

## References

* [Stacks Project, Tag 0EFQ](https://stacks.math.columbia.edu/tag/0EFQ)
* [Stacks Project, Tag 0EFK](https://stacks.math.columbia.edu/tag/0EFK)
* [Stacks Project, Tag 0DXM](https://stacks.math.columbia.edu/tag/0DXM)
* [Stacks Project, Tag 0DWV](https://stacks.math.columbia.edu/tag/0DWV)
* [Stacks Project, Tag 02IG](https://stacks.math.columbia.edu/tag/02IG)

## Tags

local cohomology, depth, annihilator, algebraization, local ring
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing PrimeSpectrum Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- A prime lies in `V(J) ∩ V(I)` iff it contains both `J` and `I`. -/
private theorem mem_zeroLocus_inter_iff {R : Type*} [CommRing R] {I J : Ideal R}
    {x : PrimeSpectrum R} :
    x ∈ PrimeSpectrum.zeroLocus (J : Set R) ∩ PrimeSpectrum.zeroLocus (I : Set R) ↔
      J ≤ x.asIdeal ∧ I ≤ x.asIdeal := by
  simp [PrimeSpectrum.mem_zeroLocus]

omit [IsNoetherianRing A] in
/-- If `V(J) ∩ V(I) = {𝔪}`, then `J ≤ 𝔪` and `I ≤ 𝔪`. -/
public theorem le_maximalIdeal_of_zeroLocus_inter_eq_closedPoint {I J : Ideal A}
    (hJ : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    J ≤ maximalIdeal A ∧ I ≤ maximalIdeal A := by
  have hmem : closedPoint A ∈
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) :=
    hJ ▸ Set.mem_singleton _
  exact mem_zeroLocus_inter_iff.1 hmem

/-- **A prime outside `V(I)` whose closed set meets `V(I)` only in `𝔪` exists as soon as some
prime avoids `V(I)` at all.** -/
private theorem exists_notMem_zeroLocus_inter_eq_closedPoint {I : Ideal A} (hI : I ≠ ⊤)
    {p : Ideal A} (hp : p.IsPrime) (hpI : ¬ I ≤ p) :
    ∃ p₀ : PrimeSpectrum A, p₀ ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧
      PrimeSpectrum.zeroLocus (p₀.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        {closedPoint A} := by
  obtain ⟨p₀, ⟨hp₀, hp₀I⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A A) {J : Ideal A | J.IsPrime ∧ ¬ I ≤ J} ⟨p, hp, hpI⟩
  have hp₀' : Ideal.IsPrime p₀ := hp₀
  obtain ⟨f, hfI, hfp₀⟩ := IsConcreteLE.not_le_iff_exists.mp hp₀I
  have hforall : ∀ q : Ideal A, q.IsPrime → p₀ < q → f ∈ q := by
    intro q hq hlt
    by_contra hfq
    exact hmax q ⟨hq, fun hIq ↦ hfq (hIq hfI)⟩ hlt
  refine ⟨⟨p₀, hp₀⟩, by simpa [PrimeSpectrum.mem_zeroLocus] using hp₀I,
    Set.Subset.antisymm (fun x hx ↦ ?_) (Set.singleton_subset_iff.2
      ⟨closedPoint_mem_zeroLocus hp₀.ne_top, closedPoint_mem_zeroLocus hI⟩)⟩
  obtain ⟨hx1, hx2⟩ := mem_zeroLocus_inter_iff.1 hx
  have hlt : p₀ < x.asIdeal := hx1.lt_of_ne fun hc ↦ hp₀I (hx2.trans_eq hc.symm)
  exact Set.mem_singleton_iff.2 (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
    (Stacks.Jacobson.NoetherianCriterion.isMaximal_of_isPrime_lt_of_forall_mem hfp₀ hforall
      x.isPrime hlt)))

/-- A Krull dimension other than `⊥` is nonnegative in the extended integers. -/
private theorem intCast_zero_le_krullDimToEInt {x : WithBot ℕ∞} (hx : x ≠ ⊥) :
    ((0 : ℤ) : EInt) ≤ krullDimToEInt x := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl hx
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      change ((0 : ℤ) : EInt) ≤ ((m : ℤ) : EInt)
      exact WithBotTop.coe_le_coe.mpr (by positivity)

variable {M : Type u} [AddCommGroup M] [Module A M]

/-- Hypothesis (6) of Stacks 0EFQ: a prime `𝔭 ∉ V(I)` whose closed set meets `V(I)` only in the
maximal ideal has `depth_{A_𝔭}(M_𝔭) > s`.

Depth is measured in `ℕ∞` and compared with the integer `s` inside `EInt` through
`Stacks.Algebraization.enatToEInt`, as in Stacks 0EFI and Stacks 0EFK. -/
public def DepthGtAtMaximalIdeal (I : Ideal A) (s : ℤ) : Prop :=
  ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
    PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A} →
    (s : EInt) < enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M))

omit [IsNoetherianRing A] in
/-- Hypothesis (6) of Stacks 0EFQ is hypothesis (6) of Stacks 0EFK at `J = 𝔪`. -/
public theorem depthGtOnAssociatedSubset_maximalIdeal_iff {I : Ideal A} (hI : I ≠ ⊤) (s : ℤ) :
    DepthGtOnAssociatedSubset (M := M) I (maximalIdeal A) s ↔
      DepthGtAtMaximalIdeal (M := M) I s := by
  constructor
  · intro h6 p hp hT
    exact h6 p hp ((mem_associatedSubset_maximalIdeal_iff hI p).2 hT)
  · intro h6 p hp hT
    exact h6 p hp ((mem_associatedSubset_maximalIdeal_iff hI p).1 hT)

variable [Module.Finite A M]

/-- **A comparison isomorphism of local cohomology.** Let `I` be an ideal of a Noetherian local
ring `(A, 𝔪)` and let `M` be a finite `A`-module satisfying hypothesis (6) of Stacks 0EFQ. For
ideals `K ≤ L ≤ 𝔪` with `V(K) ∩ V(I) = {𝔪}` the comparison `RΓ_L(M) → RΓ_K(M)` is an
isomorphism on cohomology in every degree `i ≤ s`. -/
public theorem isIso_homologyMap_localCohomologyComparison_of_zeroLocus_inter
    (I K L : Ideal A) (s : ℤ) (h6 : DepthGtAtMaximalIdeal (M := M) I s)
    (hK : PrimeSpectrum.zeroLocus (K : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (hKL : K ≤ L) (hL : L ≤ maximalIdeal A) (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyComparison A L K (Ideal.fg_of_isNoetherianRing L)
        (Ideal.fg_of_isNoetherianRing K) hKL
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) := by
  rcases lt_or_ge i 0 with hneg | hi0
  · exact ⟨0, (isZero_localCohomologyModule_of_neg A L (Ideal.fg_of_isNoetherianRing L)
      (ModuleCat.of A M) i hneg).eq_of_src _ _,
      (isZero_localCohomologyModule_of_neg A K (Ideal.fg_of_isNoetherianRing K)
        (ModuleCat.of A M) i hneg).eq_of_tgt _ _⟩
  have hIm : I ≤ maximalIdeal A := (le_maximalIdeal_of_zeroLocus_inter_eq_closedPoint hK).2
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hIm
  refine isIso_localCohomologyModuleMapOfLE A K L (Ideal.fg_of_isNoetherianRing K)
    (Ideal.fg_of_isNoetherianRing L) hKL (ModuleCat.of A M) i hi0 ?_
  intro p hp hKp hLp
  have hpI : ¬ I ≤ p := by
    intro hIp
    have hmem := (mem_zeroLocus_inter_iff (x := ⟨p, hp⟩)).2 ⟨hKp, hIp⟩
    rw [hK, Set.mem_singleton_iff] at hmem
    have hpm : p = maximalIdeal A := congrArg PrimeSpectrum.asIdeal hmem
    exact hLp (hL.trans (le_of_eq hpm.symm))
  have hpT : PrimeSpectrum.zeroLocus (p : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A} := by
    refine Set.Subset.antisymm (fun x hx ↦ ?_) (Set.singleton_subset_iff.2 ?_)
    · rw [← hK]
      exact ⟨PrimeSpectrum.zeroLocus_anti_mono_ideal hKp hx.1, hx.2⟩
    · exact ⟨closedPoint_mem_zeroLocus hp.ne_top, closedPoint_mem_zeroLocus hItop⟩
  have hdepth := h6 ⟨p, hp⟩ (by simpa [PrimeSpectrum.mem_zeroLocus] using hpI) hpT
  exact ⟨isZero_localCohomologyModule_atPrime_of_lt_depth M p i
      (lt_of_le_of_lt (WithBotTop.coe_le_coe.mpr hi) hdepth),
    isZero_localCohomologyModule_atPrime_of_lt_depth M p (i - 1)
      (lt_of_le_of_lt (WithBotTop.coe_le_coe.mpr (by omega : i - 1 ≤ s)) hdepth)⟩

/-- Under hypothesis (6) the local cohomology of `M` supported in any ideal `J` with
`V(J) ∩ V(I) = {𝔪}` agrees with the local cohomology supported in `𝔪` in all degrees `i ≤ s`:
`H^i_J(M) = H^i_𝔪(M)`. -/
@[stacks 0EFQ "H^i_J(M) = H^i_𝔪(M) for i ≤ s, for every J with V(J) ∩ V(I) = {𝔪}"]
public theorem isIso_homologyMap_localCohomologyComparison_maximalIdeal
    (I J : Ideal A) (s : ℤ) (h6 : DepthGtAtMaximalIdeal (M := M) I s)
    (hJ : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyComparison A (maximalIdeal A) J
        (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) (Ideal.fg_of_isNoetherianRing J)
        (le_maximalIdeal_of_zeroLocus_inter_eq_closedPoint hJ).1
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) :=
  isIso_homologyMap_localCohomologyComparison_of_zeroLocus_inter I J (maximalIdeal A) s h6 hJ
    (le_maximalIdeal_of_zeroLocus_inter_eq_closedPoint hJ).1 le_rfl i hi

/-- **The hypotheses of Stacks 0DXM force `0 ≤ d` whenever some prime avoids `V(I)`.** The prime
`𝔭₀` of `exists_notMem_zeroLocus_inter_eq_closedPoint` is one that hypothesis (3) applies to, and
it bounds `d` below by `dim(A/𝔭₀)`, which is not negative. -/
private theorem zero_le_of_localStabilizationHypotheses {I : Ideal A} {s d : ℤ}
    {omega : DerivedCategory (ModuleCat.{u} A)}
    (H : LocalStabilizationHypotheses (M := M) I s d omega)
    {p : Ideal A} (hp : p.IsPrime) (hpI : ¬ I ≤ p) : 0 ≤ d := by
  obtain ⟨p₀, hp₀I, hp₀⟩ := exists_notMem_zeroLocus_inter_eq_closedPoint H.ne_top hp hpI
  have hprime : p₀.asIdeal.IsPrime := p₀.isPrime
  have hnt : Nontrivial (A ⧸ p₀.asIdeal) := Submodule.Quotient.nontrivial_iff.mpr hprime.ne_top
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p₀.asIdeal) :=
    zero_le_ringKrullDim_iff_nontrivial.mpr hnt
  have hne : ringKrullDim (A ⧸ p₀.asIdeal) ≠ ⊥ := fun h ↦ by simp [h] at hnn
  exact WithBotTop.coe_le_coe.mp
    ((intCast_zero_le_krullDimToEInt hne).trans (H.dimensionBound p₀ hp₀I hp₀))

section

variable (I : Ideal A) (s d : ℤ) (omega : DerivedCategory (ModuleCat.{u} A))
  (H : LocalStabilizationHypotheses (M := M) I s d omega)

/-- Under hypothesis (6) the local cohomology of `M` supported in the ideal `J₀` produced by
Stacks 0DXM agrees with the local cohomology supported in `𝔪` in all degrees `i ≤ s`:
`H^i_{J₀}(M) = H^i_𝔪(M)`. -/
@[stacks 0EFQ "H^i_{J₀}(M) = H^i_𝔪(M) for i ≤ s"]
public theorem isIso_homologyMap_localCohomologyComparison_stabilizingIdeal_maximalIdeal
    (h6 : DepthGtAtMaximalIdeal (M := M) I s) (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyComparison A (maximalIdeal A)
        (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal A))
        (Ideal.fg_of_isNoetherianRing
          (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses))
        (stabilizingIdeal_le I (maximalIdeal A) s d omega H.toStabilizationHypotheses)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) :=
  isIso_homologyMap_localCohomologyComparison_of_zeroLocus_inter I
    (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses)
    (maximalIdeal A) s h6 (zeroLocus_stabilizingIdeal_maximalIdeal_inter I s d omega H)
    (stabilizingIdeal_le I (maximalIdeal A) s d omega H.toStabilizationHypotheses) le_rfl i hi

/-- Under hypothesis (6) the local cohomology of `M` supported in the ideal `J₀` produced by
Stacks 0DXM agrees with the local cohomology supported in any further ideal `J ⊆ J₀` with
`V(J) ∩ V(I) = {𝔪}`, in all degrees `i ≤ s`: `H^i_{J₀}(M) = H^i_J(M)`. -/
@[stacks 0EFQ "H^i_{J₀}(M) = H^i_J(M) for i ≤ s"]
public theorem isIso_homologyMap_localCohomologyComparison_stabilizingIdeal_of_depthGt
    (h6 : DepthGtAtMaximalIdeal (M := M) I s) (J : Ideal A)
    (hJle : J ≤ stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses)
    (hJ : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyComparison A
        (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses) J
        (Ideal.fg_of_isNoetherianRing
          (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses))
        (Ideal.fg_of_isNoetherianRing J) hJle
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) :=
  isIso_homologyMap_localCohomologyComparison_of_zeroLocus_inter I J
    (stabilizingIdeal I (maximalIdeal A) s d omega H.toStabilizationHypotheses) s h6 hJ hJle
    (stabilizingIdeal_le I (maximalIdeal A) s d omega H.toStabilizationHypotheses) i hi

include H in
/-- Under hypothesis (6), `0 ≤ s` and `0 ≤ d`, a single power of `I` annihilates `H^i_J(M)` in
every degree `i ≤ s`, uniformly in every ideal `J` with `V(J) ∩ V(I) = {𝔪}`. -/
@[stacks 0EFQ "the annihilation assertion through Stacks 0EFK, in the numerical range 0 ≤ s and
0 ≤ d in which that lemma is stated"]
public theorem exists_pow_le_annihilator_localCohomologyModule_maximalIdeal
    (h6 : DepthGtAtMaximalIdeal (M := M) I s) (hs : 0 ≤ s) (hd : 0 ≤ d) :
    ∃ n : ℕ, ∀ J : Ideal A,
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        {closedPoint A} →
      ∀ i : ℤ, i ≤ s →
        I ^ n ≤ Module.annihilator A
          (localCohomologyModule A J (Ideal.fg_of_isNoetherianRing J)
            (ModuleCat.of A M) i) := by
  have hIm : I ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal H.ne_top
  have h6' : DepthGtOnAssociatedSubset (M := M) I (maximalIdeal A) s :=
    (depthGtOnAssociatedSubset_maximalIdeal_iff H.ne_top s).2 h6
  obtain ⟨n, hn⟩ := exists_pow_le_annihilator_localCohomologyModule_sup I (maximalIdeal A) s d
    omega H.toStabilizationHypotheses h6' hs hd
  have hsup : maximalIdeal A ⊔ I = maximalIdeal A := sup_eq_left.mpr hIm
  have hm : ∀ i : ℤ, i ≤ s →
      I ^ n ≤ Module.annihilator A
        (localCohomologyModule A (maximalIdeal A)
          (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) (ModuleCat.of A M) i) := by
    intro i hi
    have key : ∀ (K : Ideal A) (hK : K.FG), K = maximalIdeal A ⊔ I →
        I ^ n ≤ Module.annihilator A
          (localCohomologyModule A K hK (ModuleCat.of A M) i) := by
      rintro K hK rfl
      exact hn i hi
    exact key (maximalIdeal A) (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) hsup.symm
  refine ⟨n, fun J hJ i hi ↦ (hm i hi).trans (le_of_eq ?_)⟩
  have hiso := isIso_homologyMap_localCohomologyComparison_maximalIdeal I J s h6 hJ i hi
  exact (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
    (localCohomologyComparison A (maximalIdeal A) J
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) (Ideal.fg_of_isNoetherianRing J)
      (le_maximalIdeal_of_zeroLocus_inter_eq_closedPoint hJ).1
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A M))))).toLinearEquiv.annihilator_eq

include H in
/-- Under hypothesis (6) a single power of `I` annihilates `H^i_J(M)` in every degree `i ≤ s`,
uniformly in every ideal `J` with `V(J) ∩ V(I) = {𝔪}`; this includes `J = 𝔪` and `J = J₀`, by
`zeroLocus_maximalIdeal_inter` and `zeroLocus_stabilizingIdeal_maximalIdeal_inter`. -/
@[stacks 0EFQ "the annihilation assertion: a power of I annihilates H^i_J(M) for i ≤ s, for every
J with V(J) ∩ V(I) = {𝔪}, with no hypothesis beyond the tag's"]
public theorem exists_pow_le_annihilator_localCohomologyModule_maximalIdeal_of_depthGt
    (h6 : DepthGtAtMaximalIdeal (M := M) I s) :
    ∃ n : ℕ, ∀ J : Ideal A,
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        {closedPoint A} →
      ∀ i : ℤ, i ≤ s →
        I ^ n ≤ Module.annihilator A
          (localCohomologyModule A J (Ideal.fg_of_isNoetherianRing J)
            (ModuleCat.of A M) i) := by
  rcases lt_or_ge s 0 with hs | hs
  · refine ⟨0, fun J _ i hi a _ ↦ ?_⟩
    have hsub : Subsingleton (localCohomologyModule A J (Ideal.fg_of_isNoetherianRing J)
        (ModuleCat.of A M) i) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_localCohomologyModule_of_neg A J
        (Ideal.fg_of_isNoetherianRing J) (ModuleCat.of A M) i (lt_of_le_of_lt hi hs))
    exact Module.mem_annihilator.2 fun x ↦ Subsingleton.elim _ _
  by_cases hV : ∀ p : Ideal A, p.IsPrime → I ≤ p
  · have hrad : I ≤ (⊥ : Ideal A).radical := by
      rw [Ideal.radical_eq_sInf]
      exact le_sInf fun J hJ ↦ hV J hJ.2
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
      (Ideal.fg_of_isNoetherianRing I)
    exact ⟨n, fun J _ i _ ↦ hn.trans bot_le⟩
  · push Not at hV
    obtain ⟨p, hp, hpI⟩ := hV
    exact exists_pow_le_annihilator_localCohomologyModule_maximalIdeal I s d omega H h6 hs
      (zero_le_of_localStabilizationHypotheses H hp hpI)

end

end Stacks.Algebraization

end
