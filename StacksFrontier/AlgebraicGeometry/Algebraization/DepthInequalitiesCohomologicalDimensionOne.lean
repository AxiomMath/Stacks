module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.Algebraization.StalkOfIdealOnOpen
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.CompletedStalkAssociatedDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.IsolatedPrime
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit

/-!
# The `(s, s + 1)`-inequalities in cohomological dimension one

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X \ Z`, and let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`. When
`cd(A, I) = 1` the two-case condition defining the `(s, s + 1)`-inequalities collapses to a
single strict inequality: `(ℱ_n)` satisfies them exactly when

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > s + 1`

for every `y ∈ U ∩ Y` and every prime `𝔭 ⊆ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`. The cases
`s = 2` and `s = 1` are recorded separately.

## Main results

* `Stacks.Algebraization.satisfiesDepthInequalities_succ_iff`: The equivalence for an arbitrary
  bound `s`.
* `Stacks.Algebraization.satisfiesDepthInequalities_two_three_iff`: The case `s = 2`.
* `Stacks.Algebraization.satisfiesDepthInequalities_one_two_iff`: The case `s = 1`.

## Implementation notes

The source's `cd(A, I) = 1` is `Stacks.LocalCohomology.cohomologicalDimension S.A S.I _ = 1`,
the cohomological dimension of Stacks 0DX8; it takes a finite-generation witness for the ideal,
supplied by Noetherianity.

The two-case condition of `Stacks.Algebraization.SatisfiesDepthInequalities` is a conjunction of
implications on the two sides of the equality `V(𝔭) ∩ V(I𝒪_{X,y}^∧) = {𝔪_y^∧}`, and the
quantities compared are extended integers (`EInt`): the depth and the distance term may be
infinite, the dimension term may not.

## References

* [Stacks Project, Tag 0EKW](https://stacks.math.columbia.edu/tag/0EKW)
* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5), the case `s = 1`.
* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF), the conditions the
  `(s, s + 1)`-inequalities encode.
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA), change of rings.
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF), the dimension bound.
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR), dualizing complexes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.AlgebraicGeometry.CoherentPushforwardCriterion
open Stacks.AdicCompletionDimension

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Extended-integer arithmetic -/

/-- The extended-integer image of an extended natural number is never `⊥`. -/
private theorem enatToEInt_ne_bot (n : ℕ∞) : enatToEInt n ≠ ⊥ := by
  cases n using ENat.recTopCoe <;> exact WithBot.coe_ne_bot

/-- The extended-integer image of a Krull dimension other than `⊥` is not `⊥`. -/
private theorem krullDimToEInt_ne_bot {n : WithBot ℕ∞} (hn : n ≠ ⊥) :
    krullDimToEInt n ≠ ⊥ := by
  cases n using WithBot.recBotCoe with
  | bot => exact absurd rfl hn
  | coe n => cases n using ENat.recTopCoe <;> exact WithBot.coe_ne_bot

/-- A Krull dimension at least one has extended-integer image at least one. -/
private theorem one_le_krullDimToEInt {n : WithBot ℕ∞} (h : 1 ≤ n) :
    ((1 : ℤ) : EInt) ≤ krullDimToEInt n := by
  cases n using WithBot.recBotCoe with
  | bot => simp at h
  | coe n =>
    cases n using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      have hn : 1 ≤ n := by exact_mod_cast h
      change ((1 : ℤ) : EInt) ≤ ((n : ℤ) : EInt)
      exact WithBotTop.coe_le_coe.mpr (by omega)

/-- A Krull dimension other than `⊥` has extended-integer image one exactly when it is one. -/
private theorem krullDimToEInt_eq_one_iff {n : WithBot ℕ∞} (hn : n ≠ ⊥) :
    krullDimToEInt n = ((1 : ℤ) : EInt) ↔ n = 1 := by
  cases n using WithBot.recBotCoe with
  | bot => exact absurd rfl hn
  | coe n =>
    cases n using ENat.recTopCoe with
    | top =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact absurd h.symm (WithBotTop.coe_ne_top _)
      · exact absurd (WithBot.coe_injective h : (⊤ : ℕ∞) = 1) (by simp)
    | coe n =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain rfl : n = 1 := by exact_mod_cast (WithBotTop.coe_injective h : (n : ℤ) = 1)
        rfl
      · obtain rfl : n = 1 := by exact_mod_cast h
        rfl

/-- An extended integer other than `⊥` that is at least one and not one is at least two. -/
private theorem two_le_of_one_le_of_ne_one {c : EInt} (hc : c ≠ ⊥)
    (h1 : ((1 : ℤ) : EInt) ≤ c) (hne : c ≠ ((1 : ℤ) : EInt)) :
    ((2 : ℤ) : EInt) ≤ c := by
  cases c using WithBot.recBotCoe with
  | bot => exact absurd rfl hc
  | coe m =>
    cases m using WithTop.recTopCoe with
    | top => exact le_top
    | coe n =>
      have hn1 : (1 : ℤ) ≤ n := WithBotTop.coe_le_coe.mp h1
      have hnn : n ≠ 1 := fun h => hne (by rw [h]; rfl)
      change ((2 : ℤ) : EInt) ≤ ((n : ℤ) : EInt)
      exact WithBotTop.coe_le_coe.mpr (by omega)

/-! ### The extended-integer arithmetic, exported -/

/-- The extended-integer image of an extended natural number is never `⊥`. -/
public alias enatToEInt_ne_bot' := enatToEInt_ne_bot

/-- The extended-integer image of a Krull dimension other than `⊥` is not `⊥`. -/
public alias krullDimToEInt_ne_bot' := krullDimToEInt_ne_bot

/-- A Krull dimension at least one has extended-integer image at least one. -/
public alias one_le_krullDimToEInt' := one_le_krullDimToEInt

/-- A Krull dimension other than `⊥` has extended-integer image one exactly when it is one. -/
public alias krullDimToEInt_eq_one_iff' := krullDimToEInt_eq_one_iff

/-- An extended integer other than `⊥` that is at least one and not one is at least two. -/
public alias two_le_of_one_le_of_ne_one' := two_le_of_one_le_of_ne_one

/-! ### The arithmetic step -/

/-- In the extended integers `s + 1 < x + 1` exactly when `s < x`. -/
private theorem lt_add_one_iff_lt_of_int (s : ℤ) (x : EInt) :
    x + ((1 : ℤ) : EInt) > ((s + 1 : ℤ) : EInt) ↔ x > ((s : ℤ) : EInt) := by
  change ((s + 1 : ℤ) : EInt) < x + ((1 : ℤ) : EInt) ↔ ((s : ℤ) : EInt) < x
  rw [Stacks.Chow.coe_add_coe_eq_coe_add, ← Stacks.Chow.eintAddRight_apply 1 x,
    ← Stacks.Chow.eintAddRight_apply 1 ((s : ℤ) : EInt)]
  exact (Stacks.Chow.eintAddRight 1).lt_iff_lt

/-- For extended integers `d`, `c`, `e` with `c ≥ 1` and `c` finite below, the two-case
`(s, s + 1)`-condition on the two sides of `c = 1` is equivalent to the single inequality
`d + c + e > s + 1`. -/
private theorem depthInequalities_succ_arithmetic (s : ℤ) {d c e : EInt} (hc : c ≠ ⊥)
    (hcpos : ((1 : ℤ) : EInt) ≤ c) :
    ((c ≠ ((1 : ℤ) : EInt) →
          d + e ≥ ((s : ℤ) : EInt) ∨ d + c + e > ((s + 1 : ℤ) : EInt)) ∧
        (c = ((1 : ℤ) : EInt) → d + e > ((s : ℤ) : EInt))) ↔
      d + c + e > ((s + 1 : ℤ) : EInt) := by
  have hreassoc : d + c + e = d + e + c := by
    rw [add_assoc, add_comm c e, ← add_assoc]
  rw [hreassoc]
  by_cases hc1 : c = ((1 : ℤ) : EInt)
  · subst hc1
    rw [lt_add_one_iff_lt_of_int]
    exact ⟨fun h => h.2 rfl, fun h => ⟨fun hne => absurd rfl hne, fun _ => h⟩⟩
  · have hc2 : ((2 : ℤ) : EInt) ≤ c := two_le_of_one_le_of_ne_one hc hcpos hc1
    refine ⟨fun h => ?_, fun h => ⟨fun _ => Or.inr h, fun hcc => absurd hcc hc1⟩⟩
    rcases h.1 hc1 with hge | hgt
    · have hsum : ((s : ℤ) : EInt) + ((2 : ℤ) : EInt) ≤ d + e + c := add_le_add hge hc2
      refine lt_of_lt_of_le ?_ hsum
      rw [← Stacks.Chow.coe_add_coe_eq_coe_add]
      exact WithBotTop.coe_lt_coe.mpr (by omega)
    · exact hgt

/-! ### Normalized dualizing complexes on completions -/

/-- **The completion of a Noetherian local ring carries a normalized dualizing complex.** -/
private theorem exists_isNormalizedDualizingComplex_adicCompletion (B : Type u) [CommRing B]
    [IsNoetherianRing B] [IsLocalRing B] :
    ∃ ω : DerivedCategory (ModuleCat.{u} (AdicCompletion (maximalIdeal B) B)),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω := by
  obtain ⟨ω, hω⟩ :=
    Dualizing.exists_isNormalizedDualizingComplex_of_isPrecomplete_maximalIdeal
      (AdicCompletion (maximalIdeal B) B)
  exact ⟨ω, Stacks.LocalCohomology.isNormalizedDualizingComplex_of_ulift_zero hω⟩

/-! ### The closed fibre through a prime, in cohomological dimension one -/

section RingTheory

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The quotient of a local ring by a prime ideal is a local ring. -/
local instance isLocalRingQuotientPrime (p : Ideal R) [p.IsPrime] : IsLocalRing (R ⧸ p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

omit [IsNoetherianRing R] in
/-- The set of primes through `𝔭` in `V(J)`, written as a set of ideals, is the closed point
alone exactly when the corresponding intersection of zero loci is. -/
private theorem zeroLocus_inter_eq_singleton (J p : Ideal R)
    (huniq : {q : Ideal R | q.IsPrime ∧ p ≤ q ∧ J ≤ q} = {maximalIdeal R}) :
    PrimeSpectrum.zeroLocus (p : Set R) ∩ PrimeSpectrum.zeroLocus (J : Set R) =
      {closedPoint R} := by
  have hmem : maximalIdeal R ∈ {q : Ideal R | q.IsPrime ∧ p ≤ q ∧ J ≤ q} := by
    rw [huniq]; exact Set.mem_singleton _
  ext q
  constructor
  · rintro ⟨hpq, hJq⟩
    have hmem : q.asIdeal ∈ {r : Ideal R | r.IsPrime ∧ p ≤ r ∧ J ≤ r} := ⟨q.isPrime, hpq, hJq⟩
    rw [huniq] at hmem
    exact PrimeSpectrum.ext (by simpa [closedPoint] using hmem)
  · rintro rfl
    exact ⟨(PrimeSpectrum.mem_zeroLocus _ _).mpr hmem.2.1,
      (PrimeSpectrum.mem_zeroLocus _ _).mpr hmem.2.2⟩

omit [IsNoetherianRing R] in
/-- If `dim(R/𝔭) = 1` then the primes containing both `𝔭` and a
proper ideal `J` not contained in `𝔭` are exactly the maximal ideal. -/
private theorem fibre_eq_singleton_of_ringKrullDim_quotient_eq_one (J p : Ideal R)
    [hp : p.IsPrime] (hJm : J ≤ maximalIdeal R) (hJp : ¬ J ≤ p)
    (hdim : ringKrullDim (R ⧸ p) = 1) :
    {q : Ideal R | q.IsPrime ∧ p ≤ q ∧ J ≤ q} = {maximalIdeal R} := by
  classical
  have hdimLE : Ring.KrullDimLE 1 (R ⧸ p) := Ring.krullDimLE_iff.mpr hdim.le
  have hprimeOne (q : Ideal (R ⧸ p)) (hq : q.IsPrime) (hqne : q ≠ ⊥) : q.IsMaximal :=
    (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdimLE) q hqne hq
  ext q
  constructor
  · rintro ⟨hq, hpq, hJq⟩
    have hqne : q.map (Ideal.Quotient.mk p) ≠ ⊥ := by
      intro hzero
      have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk p)) hzero
      rw [Ideal.comap_map_quotientMk p q] at hcomap
      have hker : Ideal.comap (Ideal.Quotient.mk p) (⊥ : Ideal (R ⧸ p)) = p := by
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      rw [hker] at hcomap
      have hqle : q ≤ p := le_sup_right.trans hcomap.le
      exact hJp ((le_antisymm hqle hpq) ▸ hJq)
    have hqmax : (q.map (Ideal.Quotient.mk p)).IsMaximal :=
      hprimeOne _ (Ideal.isPrime_map_quotientMk_of_isPrime hpq) hqne
    have hqmap : q.map (Ideal.Quotient.mk p) = maximalIdeal (R ⧸ p) :=
      IsLocalRing.eq_maximalIdeal hqmax
    have hqpre : (q.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = q := by
      rw [Ideal.comap_map_quotientMk p q, sup_eq_right.mpr hpq]
    have : IsLocalHom (Ideal.Quotient.mk p) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [hqmap, IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk p)] at hqpre
    exact hqpre.symm
  · rintro rfl
    exact ⟨(maximalIdeal.isMaximal R).isPrime, le_maximalIdeal hp.ne_top, hJm⟩

/-- If `cd(R, J) ≤ 1` and the primes containing both `𝔭` and `J` are exactly the maximal
ideal, then `dim(R/𝔭) = 1`. -/
private theorem ringKrullDim_quotient_eq_one_of_fibre_eq_singleton (J p : Ideal R)
    [hp : p.IsPrime] (hJp : ¬ J ≤ p)
    (huniq : {q : Ideal R | q.IsPrime ∧ p ≤ q ∧ J ≤ q} = {maximalIdeal R})
    (hcd : Stacks.LocalCohomology.cohomologicalDimension R J (IsNoetherian.noetherian J) ≤ 1) :
    ringKrullDim (R ⧸ p) = 1 := by
  classical
  have hJm : J ≤ maximalIdeal R := by
    have hmem : maximalIdeal R ∈ {q : Ideal R | q.IsPrime ∧ p ≤ q ∧ J ≤ q} := by
      rw [huniq]; exact Set.mem_singleton _
    exact hmem.2.2
  have hpm : p ≠ maximalIdeal R := fun h => hJp (h ▸ hJm)
  have hdimpos : 1 ≤ ringKrullDim (R ⧸ p) :=
    one_le_ringKrullDim_quotient_of_ne_maximalIdeal p hpm
  have hzero := zeroLocus_inter_eq_singleton J p huniq
  have hbot : ringKrullDim (R ⧸ p) ≠ ⊥ := ne_of_gt (lt_of_lt_of_le (by simp) hdimpos)
  have htop : ringKrullDim (R ⧸ p) ≠ ⊤ := ringKrullDim_ne_top
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (R ⧸ p) = (n : WithBot ℕ∞) := by
    cases hd : ringKrullDim (R ⧸ p) with
    | bot => exact absurd hd hbot
    | coe m =>
      cases m with
      | top => exact absurd hd htop
      | coe k => exact ⟨k, rfl⟩
  have hle : (n : ℤ) ≤ Stacks.LocalCohomology.cohomologicalDimension R J
      (IsNoetherian.noetherian J) :=
    Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension R p J
      (IsNoetherian.noetherian J) hzero n hn
      (exists_isNormalizedDualizingComplex_adicCompletion (R ⧸ p))
  have hn1 : (n : ℤ) ≤ 1 := hle.trans hcd
  have hnge : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    rw [hn, hn0] at hdimpos
    exact absurd hdimpos (by simp)
  have : n = 1 := by omega
  rw [hn, this]
  rfl

/-- Over a Noetherian local ring of cohomological dimension at most one for `J`, a prime `𝔭`
not containing `J` has `V(𝔭) ∩ V(J) = {𝔪}` exactly when `dim(R/𝔭) = 1`. -/
private theorem fibre_eq_singleton_iff_ringKrullDim_quotient_eq_one (J p : Ideal R)
    [hp : p.IsPrime] (hJm : J ≤ maximalIdeal R) (hJp : ¬ J ≤ p)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension R J (IsNoetherian.noetherian J) ≤ 1) :
    {q : Ideal R | q.IsPrime ∧ p ≤ q ∧ J ≤ q} = {maximalIdeal R} ↔
      ringKrullDim (R ⧸ p) = 1 :=
  ⟨fun h => ringKrullDim_quotient_eq_one_of_fibre_eq_singleton J p hJp h hcd,
    fun h => fibre_eq_singleton_of_ringKrullDim_quotient_eq_one J p hJm hJp h⟩

/-- The maximal ideal of the adic completion of a Noetherian local ring along an ideal inside the
maximal ideal is the extension of the maximal ideal. -/
private theorem maximalIdeal_adicCompletion_eq_map (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    letI := isLocalRing_adicCompletion_of_le_maximalIdeal I hI
    maximalIdeal (AdicCompletion I R) = (maximalIdeal R).map (algebraMap R (AdicCompletion I R)) :=
  let := isLocalRing_adicCompletion_of_le_maximalIdeal I hI
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le I (maximalIdeal R) hI
    (Ideal.fg_of_isNoetherianRing I))).symm

end RingTheory

/-! ### The stalk of `I𝒪_U` at a point of `U ∩ Y` -/

/-- The cohomological dimension of `I𝒪_{X,y}^∧` is at most that of `I`, the ideal being the
image of `I` along `A → 𝒪_{X,y}^∧`. -/
private theorem cohomologicalDimension_completedLocalIdeal_le
    (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) (d : ℤ)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) ≤ d) :
    Stacks.LocalCohomology.cohomologicalDimension (completedLocalRing (idealOnOpen S) y)
      (completedLocalIdeal (idealOnOpen S) y) (IsNoetherian.noetherian _) ≤ d := by
  let φ : S.A →+* completedLocalRing (idealOnOpen S) y :=
    (algebraMap (S.U.toScheme.presheaf.stalk y)
      (completedLocalRing (idealOnOpen S) y)).comp (baseToPointStalk S y)
  have hmap : completedLocalIdeal (idealOnOpen S) y = S.I.map φ := by
    change (IdealSheafData.stalk (idealOnOpen S) y).map
        (algebraMap (S.U.toScheme.presheaf.stalk y)
          (completedLocalRing (idealOnOpen S) y)) = S.I.map φ
    rw [show S.I.map φ = (S.I.map (baseToPointStalk S y)).map
        (algebraMap (S.U.toScheme.presheaf.stalk y)
          (completedLocalRing (idealOnOpen S) y)) from (Ideal.map_map _ _).symm]
    exact congrArg (fun J => Ideal.map (algebraMap (S.U.toScheme.presheaf.stalk y)
      (completedLocalRing (idealOnOpen S) y)) J) (stalk_idealOnOpen_eq_map S y)
  rw [Stacks.LocalCohomology.cohomologicalDimension_congr (IsNoetherian.noetherian _)
    (IsNoetherian.noetherian _) hmap]
  exact (Stacks.LocalCohomology.cohomologicalDimension_map_le φ S.I
    (IsNoetherian.noetherian S.I)).trans hcd

/-- The `(s, s + 1)`-inequalities collapse to a single strict inequality when `cd(A, I) = 1`. -/
private theorem satisfiesDepthInequalities_succ_iff_aux (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1) (s : ℤ) :
    SatisfiesDepthInequalities S F s (s + 1) ↔
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          depthAddDimAddDistance S F y z p > ((s + 1 : ℤ) : EInt) := by
  classical
  have key : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
        ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
        (((adicClosedFibreThrough (idealOnOpen S) y p ≠
                  {completedMaximalIdeal (idealOnOpen S) y} →
                depthAddDistance S F y z p ≥ ((s : ℤ) : EInt) ∨
                  depthAddDimAddDistance S F y z p > ((s + 1 : ℤ) : EInt)) ∧
              (adicClosedFibreThrough (idealOnOpen S) y p =
                  {completedMaximalIdeal (idealOnOpen S) y} →
                depthAddDistance S F y z p > ((s : ℤ) : EInt))) ↔
            depthAddDimAddDistance S F y z p > ((s + 1 : ℤ) : EInt)) := by
    intro y z hyz p hpJ
    let hlocal : IsLocalRing (completedLocalRing (idealOnOpen S) y) :=
      isLocalRing_adicCompletion_of_le_maximalIdeal _
        (stalk_idealOnOpen_le_maximalIdeal S y z hyz)
    have hJm : completedLocalIdeal (idealOnOpen S) y ≤
        maximalIdeal (completedLocalRing (idealOnOpen S) y) := by
      rw [maximalIdeal_adicCompletion_eq_map _
        (stalk_idealOnOpen_le_maximalIdeal S y z hyz)]
      exact Ideal.map_mono (stalk_idealOnOpen_le_maximalIdeal S y z hyz)
    have hmax : completedMaximalIdeal (idealOnOpen S) y =
        maximalIdeal (completedLocalRing (idealOnOpen S) y) :=
      (maximalIdeal_adicCompletion_eq_map _
        (stalk_idealOnOpen_le_maximalIdeal S y z hyz)).symm
    have hpne : p.asIdeal ≠ maximalIdeal (completedLocalRing (idealOnOpen S) y) := fun h =>
      hpJ (h ▸ hJm)
    have : p.asIdeal.IsPrime := p.isPrime
    have hdimpos : 1 ≤ ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) :=
      one_le_ringKrullDim_quotient_of_ne_maximalIdeal p.asIdeal hpne
    have hcdle := cohomologicalDimension_completedLocalIdeal_le S y 1 hcd.le
    have hbridge := fibre_eq_singleton_iff_ringKrullDim_quotient_eq_one
      (completedLocalIdeal (idealOnOpen S) y) p.asIdeal hJm hpJ hcdle
    have hcbot : ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le (by simp) hdimpos)
    have hcondition : adicClosedFibreThrough (idealOnOpen S) y p =
          {completedMaximalIdeal (idealOnOpen S) y} ↔
        krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) =
          ((1 : ℤ) : EInt) := by
      rw [krullDimToEInt_eq_one_iff hcbot, hmax]
      exact hbridge
    have harith := depthInequalities_succ_arithmetic s
      (d := enatToEInt (completedStalkDepth (idealOnOpen S) F y p))
      (c := krullDimToEInt
        (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)))
      (e := enatToEInt (S.distanceToZ z))
      (krullDimToEInt_ne_bot hcbot) (one_le_krullDimToEInt hdimpos)
    have hdd : depthAddDimAddDistance S F y z p =
        enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
            krullDimToEInt
              (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) +
          enatToEInt (S.distanceToZ z) := rfl
    have hda : depthAddDistance S F y z p =
        enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
          enatToEInt (S.distanceToZ z) := rfl
    rw [hdd, hda]
    exact (and_congr (imp_congr_left (not_congr hcondition)) (imp_congr_left hcondition)).trans
      harith
  exact ⟨fun h y z hyz p hpJ => (key y z hyz p hpJ).mp (h y z hyz p hpJ),
    fun h y z hyz p hpJ => (key y z hyz p hpJ).mpr (h y z hyz p hpJ)⟩

/-! ### Stacks 0EKW -/

/-- In Situation 0EHC let `(ℱ_n)` be an object of
`Coh(U, I𝒪_U)`. If `cd(A, I) = 1`, then `(ℱ_n)` satisfies the `(2, 3)`-inequalities if and only
if `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > 3` for all `y ∈ U ∩ Y` and all primes
`𝔭 ⊆ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`. -/
@[stacks 0EKW]
public theorem satisfiesDepthInequalities_two_three_iff (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1) :
    SatisfiesDepthInequalities S F 2 3 ↔
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          depthAddDimAddDistance S F y z p > ((3 : ℤ) : EInt) :=
  satisfiesDepthInequalities_succ_iff_aux S F hcd 2

/-! ### The equivalence at an arbitrary bound -/

/-- **The collapse of the `(s, s + 1)`-inequalities in cohomological dimension one.** In
Situation 0EHC let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`. If `cd(A, I) = 1`, then `(ℱ_n)`
satisfies the `(s, s + 1)`-inequalities if and only if
`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > s + 1` for all `y ∈ U ∩ Y` and all primes
`𝔭 ⊆ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`. -/
public theorem satisfiesDepthInequalities_succ_iff (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1) (s : ℤ) :
    SatisfiesDepthInequalities S F s (s + 1) ↔
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          depthAddDimAddDistance S F y z p > ((s + 1 : ℤ) : EInt) :=
  satisfiesDepthInequalities_succ_iff_aux S F hcd s

/-! ### The opening step of Stacks 0EL5 -/

/-- In Situation 0EHC let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)` and assume `cd(A, I) = 1`.
Then `(ℱ_n)` satisfies the `(1, 2)`-inequalities if and only if

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > 2`

for every `y ∈ U ∩ Y` and every prime `𝔭 ⊆ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`. -/
@[stacks 0EL5 "only the opening step, as an equivalence: the depth hypothesis is the \
(1, 2)-inequalities, this library's encoding of conditions (b), (c), (d) of 0EJF at d = 1; in \
the affine Situation 0EHC, with the distance function for dim(closure q) and with cd(A, I) = 1 \
hypothesised; the conclusion that the system is a completion is not proved"]
public theorem satisfiesDepthInequalities_one_two_iff (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1) :
    SatisfiesDepthInequalities S F 1 2 ↔
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          depthAddDimAddDistance S F y z p > ((2 : ℤ) : EInt) :=
  satisfiesDepthInequalities_succ_iff S F hcd 1

end Stacks.Algebraization

end
