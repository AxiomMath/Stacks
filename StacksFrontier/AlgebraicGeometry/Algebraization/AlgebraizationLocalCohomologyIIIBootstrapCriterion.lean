module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthAdicCompletion
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthDimAdicCompletion
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.Normalized
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.IsolatedPrime
public import StacksFrontier.RingTheory.LocalCohomology.CutoffLocalization
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit

/-!
# A depth criterion for the bootstrap situation

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` with a dualizing complex, let `M` be a finite
`A`-module and let `s`, `d` be integers with `cd(A, I) ≤ d`. Suppose that for every prime
`p ∉ V(I)` and every `q ∈ V(p) ∩ V(𝔞)` either `depth(M_p) > s` or
`depth(M_p) + dim((A/p)_q) > d + s`. Then `A`, `I`, `V(𝔞)`, `M`, `s`, `d` form a bootstrap
situation.

## Main results

* `Stacks.Algebraization.exists_bootstrapSituation_of_depth_gt_or_depth_add_dim_gt` — the
  criterion, producing a `BootstrapSituation` whose ring, ideal, module, locus and integer
  bounds are the given data.

## Implementation notes

The closed locus `V(𝔞)` is contained in `V(I)` and is stable under specialization because it is
closed, and the dualizing-complex and cohomological-dimension assumptions are the first two
assumptions of the situation verbatim. The depth assumption of the situation is weaker than the
hypothesis here, which is applied to the two ends of the chain of primes. The remaining
assumption, on the completed localization `A' = (A_q)^∧` at a point `q` of `V(𝔞)`, is the
substance: a prime `p'` of `A'` meeting the adic locus only in the closed point has
`dim(A'/p') ≤ cd(A', I') ≤ cd(A, I) ≤ d`, and the depth of the completed module at `p'` is
compared with the depth of `M` at the image `p` of `p'` in `A`.

Three library results enter the proof of the substantial assumption: Stacks 0DXF, the bound
`dim(A'/p') ≤ cd(A', I')`, as
`Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension'`, which has Stacks 0BFR
for the completion of a Noetherian local ring already discharged inside it; and the second
display of Stacks 0EHW — the invariance of depth plus dimension under adic completion — as
`Module.depth_add_ringKrullDim_quotient_adicCompletion`.

Depth and dimension are compared in the extended integers through `enatToEInt` and
`krullDimToEInt`, as in the bootstrap situation itself.

## References

* [Stacks Project, Tag 0EFW](https://stacks.math.columbia.edu/tag/0EFW)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA)
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
-/

@[expose] public section

open CategoryTheory IsLocalRing
open Stacks.AdicCompletionDimension

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-- `krullDimToEInt` agrees with `enatToEInt` on the values that are not `⊥`. -/
private theorem krullDimToEInt_coe (x : ℕ∞) :
    krullDimToEInt (x : WithBot ℕ∞) = enatToEInt x := by
  cases x with
  | top => rfl
  | coe n => rfl

/-- `enatToEInt` is additive. -/
private theorem enatToEInt_add (x y : ℕ∞) :
    enatToEInt (x + y) = enatToEInt x + enatToEInt y := by
  cases x with
  | top =>
    cases y with
    | top => rfl
    | coe n =>
      change enatToEInt (⊤ : ℕ∞) = (⊤ : EInt) + (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      change (⊤ : EInt) = ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) +
        (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      rw [← WithBot.coe_add, WithTop.top_add]
      rfl
  | coe m =>
    cases y with
    | top =>
      change enatToEInt (⊤ : ℕ∞) =
        (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) + (⊤ : EInt)
      change (⊤ : EInt) = (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) +
        ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ))
      rw [← WithBot.coe_add, WithTop.add_top]
      rfl
    | coe n =>
      change enatToEInt ((m : ℕ∞) + (n : ℕ∞)) =
        (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) +
          (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      rw [← WithBot.coe_add, ← WithTop.coe_add, ← Nat.cast_add]
      change ((((m + n : ℕ) : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) = _
      norm_cast

/-- Translating a sum of a depth and a dimension into the extended integers. -/
private theorem krullDimToEInt_coe_add (x : ℕ∞) (y : WithBot ℕ∞) :
    krullDimToEInt ((x : WithBot ℕ∞) + y) = enatToEInt x + krullDimToEInt y := by
  cases y with
  | bot =>
    cases x with
    | top => rfl
    | coe n => rfl
  | coe z =>
    rw [← WithBot.coe_add, krullDimToEInt_coe, krullDimToEInt_coe, enatToEInt_add]

/-- A strict bound on a depth plus a dimension that is itself bounded by `d` gives a strict
bound on the depth alone. -/
private theorem enatToEInt_gt_of_add_natCast_gt {x : ℕ∞} {k s d : ℤ}
    (h : enatToEInt x + ((k : ℤ) : EInt) > ((d + s : ℤ) : EInt)) (hk : k ≤ d) :
    enatToEInt x > (s : EInt) := by
  cases x with
  | top =>
    change (⊤ : EInt) > (s : EInt)
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (s : ℤ))
  | coe m =>
    have hE : (((m : ℤ) : EInt)) + ((k : ℤ) : EInt) > ((d + s : ℤ) : EInt) := h
    change (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) +
      ((k : WithTop ℤ) : WithBot (WithTop ℤ)) >
      (((d + s : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) at hE
    rw [← WithBot.coe_add, ← WithTop.coe_add] at hE
    have hInt : (m : ℤ) + k > d + s := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hE)
    change ((m : ℤ) : EInt) > (s : EInt)
    exact WithBotTop.coe_lt_coe.mpr (by omega)

/-- Transporting a strict bound on a sum of a depth and a dimension along the invariance of that
sum, when the other dimension is a natural number bounded by `d`. -/
private theorem enatToEInt_gt_of_sum_eq {x y : ℕ∞} {D : WithBot ℕ∞} {n : ℕ} {s d : ℤ}
    (hsum : (x : WithBot ℕ∞) + ((n : ℕ) : WithBot ℕ∞) = (y : WithBot ℕ∞) + D)
    (hbig : enatToEInt y + krullDimToEInt D > ((d + s : ℤ) : EInt))
    (hnd : (n : ℤ) ≤ d) :
    enatToEInt x > (s : EInt) := by
  refine enatToEInt_gt_of_add_natCast_gt (k := (n : ℤ)) ?_ hnd
  have hE := congrArg krullDimToEInt hsum
  rw [krullDimToEInt_coe_add, krullDimToEInt_coe_add, krullDimToEInt_natCast] at hE
  rwa [hE]

/-- **Stacks Project, Tag 0EFW.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` admitting a
dualizing complex, let `M` be a finite `A`-module and let `s`, `d` be integers with
`cd(A, I) ≤ d`. If for every prime `p ∉ V(I)` and every `q ∈ V(p) ∩ V(𝔞)` either
`depth(M_p) > s` or `depth(M_p) + dim((A/p)_q) > d + s`, then `A`, `I`, `V(𝔞)`, `M`, `s`, `d`
are as in the bootstrap situation of Stacks 0EFU. -/
@[stacks 0EFW]
public theorem exists_bootstrapSituation_of_depth_gt_or_depth_add_dim_gt
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I a : Ideal A) (hIa : I ≤ a)
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (s d : ℤ)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{max u w} A), Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I
      (Ideal.fg_of_isNoetherianRing I) ≤ d)
    (hdepth : ∀ p q : PrimeSpectrum A,
      p.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      q ∈ PrimeSpectrum.zeroLocus (a : Set A) →
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) > (s : EInt)) ∨
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
        ((d + s : ℤ) : EInt))) :
    ∃ S : BootstrapSituation.{u, v, w},
      S.A = A ∧
      HEq S.commRing (inferInstance : CommRing A) ∧
      HEq S.isNoetherianRing (inferInstance : IsNoetherianRing A) ∧
      HEq S.I I ∧ S.M = M ∧
      HEq S.addCommGroup (inferInstance : AddCommGroup M) ∧
      HEq S.module (inferInstance : Module A M) ∧
      HEq S.finite (inferInstance : Module.Finite A M) ∧
      HEq S.T (PrimeSpectrum.zeroLocus (a : Set A)) ∧
      S.s = s ∧ S.d = d := by
  classical
  obtain ⟨K, hK⟩ := hdual
  refine ⟨{
    A := A
    I := I
    M := M
    T := PrimeSpectrum.zeroLocus (a : Set A)
    subset_adicLocus := by
      intro r hr
      rw [PrimeSpectrum.mem_zeroLocus] at hr ⊢
      exact hIa.trans hr
    stableUnderSpecialization :=
      (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
    s := s
    d := d
    dualizing := ⟨K, hK⟩
    cohomologicalDimension_le := hcd
    depth_or_depth_add_dimension := by
      intro p r q hpr hrq hpI _ _ hqT
      rcases hdepth p q (hpr.trans hrq) hpI hqT with h | h
      · exact Or.inl h.le
      · exact Or.inr h
    completedLocalDepth := ?_ }, rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl,
      HEq.rfl, HEq.rfl, rfl, rfl⟩
  intro q hq
  dsimp only
  set Aq := Localization.AtPrime q.asIdeal with hAq
  set Iq := Ideal.map (algebraMap A Aq) I with hIq
  set Mq := LocalizedModule q.asIdeal.primeCompl M with hMq
  set A' := AdicCompletion Iq Aq with hA'
  set I' := Ideal.map (algebraMap Aq A') Iq with hI'
  set m' := Ideal.map (algebraMap Aq A') (maximalIdeal Aq) with hm'
  intro p' hp'I huniq
  have hqa : a ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus q _).mp hq
  have hIqmax : Iq ≤ maximalIdeal Aq := by
    rw [hIq, ← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal Aq]
    exact Ideal.map_mono (hIa.trans hqa)
  have hIqfg : Iq.FG := Ideal.fg_of_isNoetherianRing Iq
  have : IsLocalRing A' := isLocalRing_adicCompletion_of_le_maximalIdeal Iq hIqmax
  have hm'max : m'.IsMaximal :=
    AdicCompletion.isMaximal_map_of_le Iq (maximalIdeal Aq) hIqmax hIqfg
  have hm'eq : m' = maximalIdeal A' := IsLocalRing.eq_maximalIdeal hm'max
  have hmemb : m' ∈ {r' : Ideal A' | r'.IsPrime ∧ p'.asIdeal ≤ r' ∧ I' ≤ r'} := by
    rw [huniq]; rfl
  obtain ⟨-, hp'm, hI'm⟩ := hmemb
  -- `V(p') ∩ V(I')` is the closed point of `A'`.
  have hzero : PrimeSpectrum.zeroLocus (p'.asIdeal : Set A') ∩
      PrimeSpectrum.zeroLocus (I' : Set A') = {IsLocalRing.closedPoint A'} := by
    ext r
    simp only [Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hpr, hIr⟩
      have hmem : r.asIdeal ∈ {r' : Ideal A' | r'.IsPrime ∧ p'.asIdeal ≤ r' ∧ I' ≤ r'} :=
        ⟨r.isPrime, SetLike.coe_subset_coe.mp hpr, SetLike.coe_subset_coe.mp hIr⟩
      rw [huniq] at hmem
      exact PrimeSpectrum.ext ((Set.mem_singleton_iff.mp hmem).trans hm'eq)
    · intro hr
      subst hr
      exact ⟨SetLike.coe_subset_coe.mpr (hp'm.trans hm'eq.le),
        SetLike.coe_subset_coe.mpr (hI'm.trans hm'eq.le)⟩
  -- The cohomological dimension of `I'` is at most `d`.
  have hcdq : Stacks.LocalCohomology.cohomologicalDimension Aq Iq hIqfg ≤
      Stacks.LocalCohomology.cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) :=
    Stacks.LocalCohomology.cohomologicalDimension_map_le (algebraMap A Aq) I
      (Ideal.fg_of_isNoetherianRing I)
  have hcd' : Stacks.LocalCohomology.cohomologicalDimension A' I'
      (Ideal.fg_of_isNoetherianRing I') ≤ d :=
    (Stacks.LocalCohomology.cohomologicalDimension_map_le (algebraMap Aq A') Iq
      hIqfg).trans (hcdq.trans hcd)
  -- `dim(A'/p') ≤ d`, by Stacks 0DXF.
  have : IsLocalRing (A' ⧸ p'.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p'.asIdeal) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ :=
    Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim (A' ⧸ p'.asIdeal)
  have hnd : (n : ℤ) ≤ d :=
    (Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension'
      A' p'.asIdeal I' (Ideal.fg_of_isNoetherianRing I') hzero n hn).trans hcd'
  -- The image of `p'` in `A_q` and in `A`.
  set pLoc := Ideal.comap (algebraMap Aq A') p'.asIdeal with hpLoc
  have : pLoc.IsPrime := Ideal.comap_isPrime _ _
  have : p'.asIdeal.LiesOver pLoc := ⟨rfl⟩
  set pOrig := Ideal.comap (algebraMap A Aq) pLoc with hpOrig
  have : pOrig.IsPrime := Ideal.comap_isPrime _ _
  have hpOrigq : pOrig ≤ q.asIdeal := by
    calc pOrig ≤ Ideal.comap (algebraMap A Aq) (maximalIdeal Aq) :=
          Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime pLoc)
      _ = q.asIdeal := IsLocalization.AtPrime.under_maximalIdeal Aq q.asIdeal
  have hpOrigmap : Ideal.map (algebraMap A Aq) pOrig = pLoc :=
    IsLocalization.map_under q.asIdeal.primeCompl Aq pLoc
  have hpLocI : ¬ Iq ≤ pLoc := fun h =>
    hp'I ((Ideal.map_mono h).trans Ideal.map_comap_le)
  have hpOrigI : (⟨pOrig, ‹pOrig.IsPrime›⟩ : PrimeSpectrum A) ∉
      PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    intro hsub
    refine hpLocI ?_
    rw [← hpOrigmap]
    exact Ideal.map_mono (SetLike.coe_subset_coe.mp hsub)
  -- The two comparisons of Stacks 0EHW, for `p'` and its image `p` in `A`.
  have hdepthEq : Module.depth (Localization.AtPrime pOrig)
        (maximalIdeal (Localization.AtPrime pOrig)) (LocalizedModule pOrig.primeCompl M) =
      Module.depth (Localization.AtPrime pLoc) (maximalIdeal (Localization.AtPrime pLoc))
        (LocalizedModule pLoc.primeCompl Mq) :=
    Stacks.LocalCohomology.depth_localizedModule_localizationLocalization
      q.asIdeal.primeCompl pLoc
  have hdepthLe : Module.depth (Localization.AtPrime pLoc)
        (maximalIdeal (Localization.AtPrime pLoc)) (LocalizedModule pLoc.primeCompl Mq) ≤
      Module.depth (Localization.AtPrime p'.asIdeal)
        (maximalIdeal (Localization.AtPrime p'.asIdeal))
        (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Mq)) :=
    Module.depth_localized_adicCompletion_le Iq pLoc p'.asIdeal
  have hdualq : ∃ Kq : DerivedCategory (ModuleCat.{max u w} Aq),
      Dualizing.IsDualizingComplex Kq :=
    ⟨_, Dualizing.isDualizingComplex_localizationAtPrime.{u, w} K hK q⟩
  have hsum : ((Module.depth (Localization.AtPrime p'.asIdeal)
          (maximalIdeal (Localization.AtPrime p'.asIdeal))
          (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Mq)) : ℕ∞) :
        WithBot ℕ∞) + ringKrullDim (A' ⧸ p'.asIdeal) =
      ((Module.depth (Localization.AtPrime pLoc) (maximalIdeal (Localization.AtPrime pLoc))
          (LocalizedModule pLoc.primeCompl Mq) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (Aq ⧸ pLoc) :=
    Module.depth_add_ringKrullDim_quotient_adicCompletion Aq hdualq Iq hIqmax Mq pLoc
      p'.asIdeal
  rw [hn] at hsum
  -- The hypothesis at the two ends `p` and `q` of the chain.
  have hkey : (enatToEInt (Module.depth (Localization.AtPrime pOrig)
          (maximalIdeal (Localization.AtPrime pOrig))
          (LocalizedModule pOrig.primeCompl M)) > (s : EInt)) ∨
      (enatToEInt (Module.depth (Localization.AtPrime pOrig)
          (maximalIdeal (Localization.AtPrime pOrig))
          (LocalizedModule pOrig.primeCompl M)) +
        krullDimToEInt (ringKrullDim (Aq ⧸ Ideal.map (algebraMap A Aq) pOrig)) >
        ((d + s : ℤ) : EInt)) :=
    hdepth ⟨pOrig, ‹pOrig.IsPrime›⟩ q hpOrigq hpOrigI hq
  rw [hpOrigmap, hdepthEq] at hkey
  rcases hkey with hlarge | hbig
  · exact lt_of_lt_of_le hlarge (enatToEInt_mono hdepthLe)
  · exact enatToEInt_gt_of_sum_eq hsum hbig hnd

end Stacks.Algebraization

end
