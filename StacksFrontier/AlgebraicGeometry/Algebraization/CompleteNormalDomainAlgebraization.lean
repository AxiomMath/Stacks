module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CohenMacaulayFreeDepthBound
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompleteNormalDomainDepthConditions
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzZeroSchemeImprovementHypotheses
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ExtensionPrincipalLocalTheorem

/-!
# Algebraization of formal vector bundles over a complete normal local domain

Let `(A, 𝔪)` be a complete Noetherian normal local domain of dimension at least four and let
`f ∈ 𝔪` be nonzero. [Stacks, Tag 0DXV] observes that assumptions (1), (2), (3), (5) and (6) of
[Stacks, Tag 0DXU] then hold for the algebraization situation with `𝔞 = 𝔪` and `I = (f)`, and
concludes that vector bundles on the formal completion of the punctured spectrum `U` along
`U ∩ V(f)` can be algebraized: an object `(ℱₙ)` of `Coh(U, f𝒪_U)` whose terms are finite locally
free `𝒪_U/fⁿ𝒪_U`-modules — assumption (4) of Tag 0DXU — is the completion of a coherent
`𝒪_U`-module.

## Main results

In the namespace `Stacks.Algebraization.CompleteNormalDomain`:

* `satisfiesDepthInequalities_two_three_of_isFiniteLocallyFreeAdic` — such a system satisfies the
  `(2, 3)`-inequalities of [Stacks, Tag 0EJ3].
* `satisfiesAssumptions_and_isCompletion_of_isFiniteLocallyFreeAdic` — [Stacks, Tag 0DXV]: the
  assumptions of Tag 0DXU hold, and every such system extends to `X` and is the completion of a
  coherent `𝒪_U`-module.

## Proof

The algebraization is obtained from [Stacks, Tag 0EJ9], the more general form of Tag 0DXU that
the source points to in the same remark, whose only hypothesis on `(ℱₙ)` is the
`(2, 3)`-inequalities. These are checked from assumption (6) of Tag 0DXU. At a point `y ∈ U ∩ V(f)`
the completed stalk `ℱ_y^∧` is free, so for a prime `𝔭` of `𝒪_{X,y}^∧` off `V(f)` its contraction
`𝔓 ⊂ A` lies off `V(f)`, below the prime `𝔮` of `y`, and satisfies
`depth(A_𝔓) + dim(A/𝔓) ≤ depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ(y)`
(`Stacks.Algebraization.exists_depth_add_dim_le_completedStalkDepth_of_free`, with
`δ(y) = dim(A/𝔮)`). Since `𝔮 ∈ V(𝔓) ∩ V(f)` differs from `𝔪`, assumption (6) bounds the left side
below by `4`. This is the second alternative of the first inequality; when
`V(𝔭) ∩ V(f𝒪_{X,y}^∧)` is the closed point, `dim(𝒪_{X,y}^∧/𝔭) ≤ 1` by Krull's principal ideal
theorem and the same bound gives `depth((ℱ_y^∧)_𝔭) + δ(y) > 2`.

## References

* [Stacks Project, Tag 0DXV](https://stacks.math.columbia.edu/tag/0DXV)
* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 0EJ9](https://stacks.math.columbia.edu/tag/0EJ9)
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization.CompleteNormalDomain

/-- Let `(A, 𝔪)` be a complete Noetherian normal local domain of dimension at least four, let
`f ∈ 𝔪` be nonzero, and let `(ℱₙ)` be an object of `Coh(U, f𝒪_U)` on the punctured spectrum `U`
whose terms are finite locally free over the infinitesimal neighbourhoods of `U ∩ V(f)`. Then
`(ℱₙ)` satisfies the `(2, 3)`-inequalities. -/
theorem satisfiesDepthInequalities_two_three_of_isFiniteLocallyFreeAdic (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsDomain A] [IsIntegrallyClosed A] (hdim : (4 : WithBot ℕ∞) ≤ ringKrullDim A) (f : A)
    (hfm : f ∈ maximalIdeal A)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen (completeNormalSituation A f hfm)))
    (hF : IsFiniteLocallyFreeAdic (idealOnOpen (completeNormalSituation A f hfm)) F) :
    SatisfiesDepthInequalities (completeNormalSituation A f hfm) F 2 3 := by
  let S := completeNormalSituation A f hfm
  have _ : IsLocalRing S.A := ‹IsLocalRing A›
  have _ : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  have hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K :=
    Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal A
  intro y z hyz p hp
  let q := underlyingPrime S y
  obtain ⟨P, hPI, hPq, hle⟩ := exists_depth_add_dim_le_completedStalkDepth_of_free S hdual F y z
    hyz p hp (free_localizedModule_completedStalk_of_isFiniteLocallyFreeAdic S F hF y z hyz p)
  -- `f ∉ 𝔓`, `f ∈ 𝔮` and `𝔮 ≠ 𝔪`.
  have hfP : f ∉ P.asIdeal := fun h =>
    hPI ((Ideal.span_singleton_le_iff_mem (I := P.asIdeal)).mpr h)
  have hIq : S.I ≤ q.asIdeal := by
    rw [show q.asIdeal = z.asIdeal.comap (Ideal.Quotient.mk S.I) from
      congrArg PrimeSpectrum.asIdeal hyz, ← Ideal.map_le_iff_le_comap, Ideal.map_quotient_self]
    exact bot_le
  have hfq : f ∈ q.asIdeal := hIq (Ideal.mem_span_singleton_self f)
  have hqa : ¬ S.a ≤ q.asIdeal := by
    have hmem : S.U.ι.base y ∈ (S.U : Set S.X) := by
      rw [← Scheme.Opens.range_ι S.U]; exact ⟨y, rfl⟩
    exact (PrimeSpectrum.mem_zeroLocus _ _).not.1 hmem
  -- Assumption (6) of Tag 0DXU at `𝔓`.
  have h6 := three_lt_depth_add_ringKrullDim_quotient A hdim f hfm P hfP (by
    intro heq
    have hmq := (Set.ext_iff.mp heq q).mp ⟨hPq, hfq⟩
    exact hqa (le_of_eq (congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hmq)).symm))
  -- The distance `δ(y)` is `dim(A/𝔮)`.
  obtain ⟨K, hK⟩ := hdual
  have hucat : Ring.IsUniversallyCatenary (S.A ⧸ S.I) :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective
      (Dualizing.isUniversallyCatenary_of_isDualizingComplex hK)
  have hcat : Ring.IsCatenary (S.A ⧸ S.I) := hucat (S.A ⧸ S.I)
  have hδ : ((S.distanceToZ z : ℕ∞) : WithBot ℕ∞) = ringKrullDim (S.A ⧸ q.asIdeal) := by
    rw [distanceToZEqCoheight_of_isCatenary_quotient S rfl hcat z]
    exact coheight_eq_ringKrullDim_quotient_underlyingPrime S y z hyz
  have h3 : ((3 : ℕ) : WithBot ℕ∞) <
      (completedStalkDepth (idealOnOpen S) F y p : WithBot ℕ∞) +
        ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) +
        (S.distanceToZ z : WithBot ℕ∞) := by
    rw [hδ]
    exact lt_of_lt_of_le h6 hle
  refine ⟨fun _ => Or.inr ?_, fun hsing => ?_⟩
  · exact natCast_lt_enatToEInt_add_krullDimToEInt_add_enatToEInt 3 h3
  · -- `V(𝔭) ∩ V(f𝒪_{X,y}^∧)` is the closed point, so `dim(𝒪_{X,y}^∧/𝔭) ≤ 1`.
    have hy : y ∈ (idealOnOpen S).support := by
      by_contra h
      have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support (idealOnOpen S) y).mpr h
      exact (maximalIdeal.isMaximal _).ne_top
        (top_le_iff.mp (htop ▸ stalk_idealOnOpen_le_maximalIdeal S y z hyz))
    have hst : IdealSheafData.stalk (idealOnOpen S) y =
        Ideal.span {baseToPointStalk S y (show S.A from f)} := by
      rw [stalk_idealOnOpen_eq_map, show S.I = Ideal.span {(show S.A from f)} from rfl,
        Ideal.map_span, Set.image_singleton]
    have ha : completedLocalIdeal (idealOnOpen S) y = Ideal.span
        {algebraMap (S.U.toScheme.presheaf.stalk y) (completedLocalRing (idealOnOpen S) y)
          (baseToPointStalk S y (show S.A from f))} := by
      calc completedLocalIdeal (idealOnOpen S) y
          = (Ideal.span {baseToPointStalk S y (show S.A from f)}).map
              (algebraMap (S.U.toScheme.presheaf.stalk y)
                (completedLocalRing (idealOnOpen S) y)) :=
            congrArg (fun J => J.map (algebraMap (S.U.toScheme.presheaf.stalk y)
              (completedLocalRing (idealOnOpen S) y))) hst
        _ = _ := by rw [Ideal.map_span, Set.image_singleton]
    have hc := ringKrullDim_quotient_le_one_of_adicClosedFibreThrough_eq (idealOnOpen S) hy ha
      p hsing
    set D := completedStalkDepth (idealOnOpen S) F y p
    set δ := S.distanceToZ z
    have h3' : ((3 : ℕ∞) : WithBot ℕ∞) < ((D + 1 + δ : ℕ∞) : WithBot ℕ∞) := by
      push_cast
      exact lt_of_lt_of_le h3 (add_le_add (add_le_add le_rfl hc) le_rfl)
    have h2 : (2 : ℕ∞) < D + δ := by
      have h := WithBot.coe_lt_coe.mp h3'
      rw [add_right_comm, show (3 : ℕ∞) = 2 + 1 by norm_num] at h
      exact (ENat.add_lt_add_iff_right ENat.one_ne_top).mp h
    have h3le : (3 : ℕ∞) ≤ D + δ :=
      calc (3 : ℕ∞) = 2 + 1 := by norm_num
        _ ≤ D + δ := Order.add_one_le_of_lt h2
    have hm := krullDimToEInt_mono (WithBot.coe_le_coe.mpr h3le)
    simp only [WithBot.coe_add, krullDimToEInt_add, krullDimToEInt_coe] at hm
    refine lt_of_lt_of_le ?_ hm
    change ((2 : ℤ) : EInt) < ((3 : ℤ) : EInt)
    exact WithBotTop.coe_lt_coe.mpr (by norm_num)

/-- **Stacks Project, Tag 0DXV.** Let `(A, 𝔪)` be a complete Noetherian normal local domain of
dimension at least four and let `f ∈ 𝔪` be nonzero. Then the algebraization situation with
`𝔞 = 𝔪` and `I = (f)` satisfies assumptions (1), (2), (3), (5) and (6) of [Stacks, Tag 0DXU]:
`𝔞` is the maximal ideal, `A` has a dualizing complex, `I` is generated by the nonzerodivisor `f`,
and the two depth-dimension inequalities hold off the closed point. Thus vector bundles on the
formal completion of the punctured spectrum `U` along `U ∩ V(f)` can be algebraized: every object
`(ℱₙ)` of `Coh(U, f𝒪_U)` whose terms are finite locally free over the infinitesimal neighbourhoods
of `U ∩ V(f)` extends to `X` and is the completion of a coherent `𝒪_U`-module. -/
@[stacks 0DXV "assumptions (1), (2), (3), (5) and (6) of Lemma 0DXU hold, and every object of \
Coh(U, f O_U) with finite locally free terms (a vector bundle on the formal completion of U along \
U ∩ V(f)) extends to X and is the completion of a coherent O_U-module, by Lemma 0EJ9"]
theorem satisfiesAssumptions_and_isCompletion_of_isFiniteLocallyFreeAdic (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsDomain A] [IsIntegrallyClosed A] (hdim : (4 : WithBot ℕ∞) ≤ ringKrullDim A) (f : A)
    (hfm : f ∈ maximalIdeal A) (hf : f ≠ 0) :
    ((completeNormalSituation A f hfm).a = maximalIdeal A ∧
      (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) ∧
      ((completeNormalSituation A f hfm).I = Ideal.span {f} ∧ IsSMulRegular A f) ∧
      (∀ p : PrimeSpectrum A, f ∈ p.asIdeal →
        p.asIdeal ≠ maximalIdeal A →
        (1 : WithBot ℕ∞) <
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule.AtPrime p.asIdeal (A ⧸ Ideal.span {f})) : WithBot ℕ∞) +
            ringKrullDim (A ⧸ p.asIdeal)) ∧
      (∀ p : PrimeSpectrum A, f ∉ p.asIdeal →
        ({q : PrimeSpectrum A | p.asIdeal ≤ q.asIdeal} ∩
          {q : PrimeSpectrum A | f ∈ q.asIdeal}) ≠
          {⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩} →
        (3 : WithBot ℕ∞) <
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
            ringKrullDim (A ⧸ p.asIdeal))) ∧
    ∀ F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen (completeNormalSituation A f hfm)),
      IsFiniteLocallyFreeAdic (idealOnOpen (completeNormalSituation A f hfm)) F →
        ExtendsToX (completeNormalSituation A f hfm)
            (toKerSystem (completeNormalSituation A f hfm) F) ∧
          (completionFunctor (completeNormalSituation A f hfm).U.toScheme
            ((completeNormalSituation A f hfm).Yι.ker.comap
              (completeNormalSituation A f hfm).U.ι)).essImage
            (toKerSystem (completeNormalSituation A f hfm) F) := by
  refine ⟨satisfiesAssumptions A hdim f hfm hf, fun F hF => ?_⟩
  have _ : IsLocalRing (completeNormalSituation A f hfm).A := ‹IsLocalRing A›
  have _ : IsAdicComplete (completeNormalSituation A f hfm).I
      (completeNormalSituation A f hfm).A :=
    isAdicComplete_of_le_of_fg_of_isAdicComplete (completeNormalSituation A f hfm).I_le_a
      ‹IsAdicComplete (maximalIdeal A) A› (Ideal.fg_of_isNoetherianRing _)
  have hdual : ∃ K : DerivedCategory (ModuleCat.{u} (completeNormalSituation A f hfm).A),
      Dualizing.IsDualizingComplex K :=
    Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal A
  have hineq := satisfiesDepthInequalities_two_three_of_isFiniteLocallyFreeAdic A hdim f hfm F hF
  exact ⟨extendsToX_of_isLocalRing_of_eq_span_singleton _ F f rfl hdual rfl hineq,
    essImage_completionFunctor_of_isLocalRing_of_eq_span_singleton _ F f rfl hdual rfl hineq⟩

end Stacks.Algebraization.CompleteNormalDomain

end
