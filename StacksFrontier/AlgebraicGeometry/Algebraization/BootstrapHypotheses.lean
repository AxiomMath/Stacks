module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapDepth
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparisonLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdealCollapse

/-!
# The bootstrap situation supplies the hypotheses of the stabilization lemmas

Let `S` be a bootstrap situation with ring `A`, ideal `I`, module `M`, locus `T` and bounds `s`
and `d`, and let `I ⊆ 𝔞` be an ideal whose zero locus is contained in `T`. Then the quadruple
`A, I, 𝔞, M` satisfies the hypotheses of the stabilization and algebraization lemmas of the two
previous sections, under the extra assumptions those lemmas need on `A`.

The two depth conditions are where the situation is consumed. For a prime `𝔭 ∉ V(I)` and a
specialization `𝔮 ∈ V(𝔞) ⊆ T` of it, either some prime of `V(I) \ T` lies between the two — and
then the chain estimate of the situation applies — or none does, and the strict bound of
Tag 0EID applies. The dimension condition instead comes from the cohomological-dimension bound:
a minimal prime `𝔮` of `𝔭 + I` has `dim((A/𝔭)_𝔮) ≤ cd(A, I) ≤ d` by Tag 0DXF, and `𝔮` exists
because `I` lies in the Jacobson radical.

## Main results

* `Stacks.Algebraization.stabilizationHypotheses_and_depthGtOnAssociatedSubset` — part (A): the
  hypotheses of Stacks 0EFI and Stacks 0EFK, for `I` inside the Jacobson radical.
* `Stacks.Algebraization.algebraizationHypotheses_of_supplementaryBound` — part (B): every
  hypothesis of Stacks 0EFL except (5), for `I`-adically complete `A`.
* `Stacks.Algebraization.localStabilizationHypotheses_and_depthGtAtMaximalIdeal_of_mem` —
  part (C): the hypotheses of Stacks 0DXM and Stacks 0EFQ, for local `A` with `𝔞 = 𝔪`.
* `Stacks.Algebraization.localAlgebraizationHypotheses_of_mem` — part (D): the hypotheses of
  Stacks 0DXP, for local and `I`-adically complete `A` with `𝔞 = 𝔪`.

## Implementation notes

The hypotheses of the four lemmas are the predicates `StabilizationHypotheses`,
`DepthGtOnAssociatedSubset`, `AlgebraizationHypotheses`, `LocalStabilizationHypotheses`,
`DepthGtAtMaximalIdeal` and `LocalAlgebraizationHypotheses` of the two previous sections. Each
of the first, third, fourth and sixth is parametrised by a witness `omega` for the
dualizing-complex hypothesis, which is produced here from assumption (1) of the situation, so
the conclusions are existential in `omega`; the module universe of that witness is the one in
which the situation carries its own dualizing complex.

Stacks 0EFL has its condition (5) and the dimension function it is stated against as inputs:
part (B) of the source asserts all its hypotheses *except possibly* (5), so those are exactly
what remains to be supplied. The `𝔞 = 𝔪` hypothesis of parts (C) and (D) is spelled as the
membership of the closed point in `T`, which for `𝔞 = 𝔪` is the standing assumption
`V(𝔞) ⊆ T`.

Parts (A)–(D) all state that hypotheses *of another lemma* hold; the locus `T` of Stacks 0EFI,
Stacks 0EFK and Stacks 0EFL is `associatedSubset I 𝔞`, which is not the locus `T` of the
situation, as the source warns.

## References

* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EID](https://stacks.math.columbia.edu/tag/0EID)
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-! ### The two depth conditions -/

/-- **The chain estimate of Stacks 0EFU at the two ends of a chain.** In a bootstrap situation
`S`, for a prime `𝔭 ∉ V(I)` and a specialization `𝔮` of it lying on `V(𝔞)` for an ideal `𝔞`
with `V(𝔞) ⊆ T`, either `depth(M_𝔭) ≥ s` or `depth(M_𝔭) + dim((A/𝔭)_𝔮) > d + s`.

If some prime of `V(I) \ T` lies between `𝔭` and `𝔮` this is assumption (4) of the situation; if
none does it is the stronger bound of Stacks 0EID. -/
public theorem depth_or_depth_add_dimension_of_mem_zeroLocus
    (S : BootstrapSituation.{u, v, w}) (a : Ideal S.A)
    (haT : PrimeSpectrum.zeroLocus (a : Set S.A) ⊆ S.T)
    (p q : PrimeSpectrum S.A) (hpq : p.asIdeal ≤ q.asIdeal)
    (hp : p ∉ PrimeSpectrum.zeroLocus (S.I : Set S.A))
    (hq : q ∈ PrimeSpectrum.zeroLocus (a : Set S.A)) :
    (enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl S.M)) ≥ (S.s : EInt)) ∨
    (enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl S.M)) +
      krullDimToEInt
        (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap S.A (Localization.AtPrime q.asIdeal)))) >
      ((S.d + S.s : ℤ) : EInt)) := by
  classical
  by_cases hx : ∃ r : PrimeSpectrum S.A, p.asIdeal ≤ r.asIdeal ∧ r.asIdeal ≤ q.asIdeal ∧
      r ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) ∧ r ∉ S.T
  · obtain ⟨r, hpr, hrq, hrI, hrT⟩ := hx
    exact S.depth_or_depth_add_dimension p r q hpr hrq hp hrI hrT (haT hq)
  · exact Or.inl
      (depth_localized_gt_of_no_intermediate_prime S p q hpq hp (haT hq) hx).le

/-- **Stacks Project, Tag 0EFV, hypothesis (6) of Stacks 0EFK.** In a bootstrap situation whose
ideal `I` lies in the Jacobson radical, a prime `𝔭 ∉ V(I)` all of whose specializations on
`V(I)` lie on `V(𝔞)` has `depth(M_𝔭) > s`.

A maximal ideal containing `𝔭` contains `I`, so `V(𝔭) ∩ V(I)` has a point `𝔮`, which lies on
`V(𝔞)` and hence in `T`. No prime of `V(I) \ T` lies between `𝔭` and `𝔮`, since any prime of
`V(𝔭) ∩ V(I)` lies on `V(𝔞) ⊆ T`; so Stacks 0EID gives the strict bound. -/
@[stacks 0EFV "part (A), hypothesis (6) of Stacks 0EFK for A, I, 𝔞, M"]
public theorem depthGtOnAssociatedSubset_of_le_jacobson
    (S : BootstrapSituation.{u, u, w}) (a : Ideal S.A) (_hIa : S.I ≤ a)
    (haT : PrimeSpectrum.zeroLocus (a : Set S.A) ⊆ S.T)
    (hjac : S.I ≤ (⊥ : Ideal S.A).jacobson) :
    DepthGtOnAssociatedSubset (M := S.M) S.I a S.s := by
  intro p hp hpT
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  have hIm : S.I ≤ m := hjac.trans (sInf_le ⟨bot_le, hm⟩)
  let q : PrimeSpectrum S.A := ⟨m, hm.isPrime⟩
  refine depth_localized_gt_of_no_intermediate_prime S p q hpm hp (haT (hpT ⟨hpm, hIm⟩).1) ?_
  rintro ⟨r, hpr, -, hrI, hrT⟩
  exact hrT (haT (hpT ⟨hpr, hrI⟩).1)

/-! ### Part (A) -/

/-- **Stacks Project, Tag 0EFV, hypothesis (3) of Stacks 0EFI.** In a bootstrap situation whose
ideal `I` lies in the Jacobson radical, a prime `𝔭 ∉ V(I)` all of whose specializations on
`V(I)` lie on `V(𝔞)` has one along which the relative dimension is at most `d`.

This is Stacks 0DXF: a minimal prime `𝔮` of `𝔭 + I` has `dim((A/𝔭)_𝔮) ≤ cd(A, I) ≤ d`, and it
lies on `V(𝔞)` because it lies on `V(𝔭) ∩ V(I)`. -/
@[stacks 0EFV "part (A), hypothesis (3) of Stacks 0EFI for A, I, 𝔞, M"]
public theorem exists_mem_zeroLocus_dimension_le_of_le_jacobson
    (S : BootstrapSituation.{u, v, w}) (a : Ideal S.A)
    (hjac : S.I ≤ (⊥ : Ideal S.A).jacobson)
    (p : PrimeSpectrum S.A)
    (hpT : p ∈ associatedSubset S.I a) :
    ∃ q : PrimeSpectrum S.A,
      q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set S.A) ∩
          PrimeSpectrum.zeroLocus (a : Set S.A)) ∩
          PrimeSpectrum.zeroLocus (S.I : Set S.A) ∧
      krullDimToEInt
        (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap S.A (Localization.AtPrime q.asIdeal)))) ≤
        (S.d : EInt) := by
  obtain ⟨q, hpq, hIq, hd⟩ := exists_specialization_dimension_le_of_le_jacobson S.I hjac p S.d
    S.cohomologicalDimension_le
  exact ⟨q, ⟨⟨hpq, (hpT ⟨hpq, hIq⟩).1⟩, hIq⟩, hd⟩

/-- **Stacks Project, Tag 0EFV, part (A).** Let `S` be a bootstrap situation whose ideal `I` is
contained in the Jacobson radical of `A`, and let `I ⊆ 𝔞` be an ideal with `V(𝔞) ⊆ T`. Then all
hypotheses of Stacks 0EFI and of Stacks 0EFK hold for `A, I, 𝔞, M`.

Hypothesis (1) is assumption (1) of the situation, hypothesis (2) is empty, hypothesis (3) is
`Stacks.Algebraization.exists_mem_zeroLocus_dimension_le_of_le_jacobson`, hypothesis (4) is
`Stacks.Algebraization.depth_or_depth_add_dimension_of_mem_zeroLocus`, and the extra hypothesis
(6) of Stacks 0EFK is
`Stacks.Algebraization.depthGtOnAssociatedSubset_of_le_jacobson`. -/
@[stacks 0EFV "part (A): all hypotheses of Stacks 0EFI and Stacks 0EFK for A, I, 𝔞, M"]
public theorem stabilizationHypotheses_and_depthGtOnAssociatedSubset
    (S : BootstrapSituation.{u, u, w}) (a : Ideal S.A) (hIa : S.I ≤ a)
    (haT : PrimeSpectrum.zeroLocus (a : Set S.A) ⊆ S.T)
    (hjac : S.I ≤ (⊥ : Ideal S.A).jacobson) :
    (∃ omega : DerivedCategory (ModuleCat.{max u w} S.A),
        StabilizationHypotheses (M := S.M) S.I a S.s S.d omega) ∧
      DepthGtOnAssociatedSubset (M := S.M) S.I a S.s := by
  refine ⟨?_, depthGtOnAssociatedSubset_of_le_jacobson S a hIa haT hjac⟩
  obtain ⟨omega, homega⟩ := S.dualizing
  refine ⟨omega, homega, fun p _ hpT ↦
    exists_mem_zeroLocus_dimension_le_of_le_jacobson S a hjac p hpT, ?_⟩
  exact fun p hp _ ↦ or_iff_not_imp_left.2 fun hdep q hq ↦
    (depth_or_depth_add_dimension_of_mem_zeroLocus S a haT p q hq.1.1 hp hq.1.2).resolve_left hdep

/-! ### Part (B) -/

/-- **Stacks Project, Tag 0EFV, part (B).** Let `S` be a bootstrap situation whose ring is
`I`-adically complete, and let `I ⊆ 𝔞` be an ideal with `V(𝔞) ⊆ T`. Then all hypotheses of
Stacks 0EFL except possibly (5) hold for `A, I, 𝔞, M`: given a dimension function with its
extreme values on `V(𝔞) ∩ V(I)` and given condition (5), the hypotheses of that lemma hold in
full.

Condition (1) is the completeness together with assumption (1) of the situation, condition (2)
is empty, condition (3) is assumption (3) of the situation, and condition (4) is the same as
condition (4) of Stacks 0EFI, proved in part (A). -/
@[stacks 0EFV "part (B): all hypotheses of Stacks 0EFL except possibly (5) for A, I, 𝔞, M"]
public theorem algebraizationHypotheses_of_supplementaryBound
    (S : BootstrapSituation.{u, u, w}) (a : Ideal S.A) (_hIa : S.I ≤ a)
    (haT : PrimeSpectrum.zeroLocus (a : Set S.A) ⊆ S.T)
    (hcomplete : IsAdicComplete S.I S.A)
    (δ : PrimeSpectrum S.A → ℤ) (δmax δmin : ℤ)
    (hδ : IsDimensionFunctionProp δ)
    (hmax : IsGreatest (δ '' (PrimeSpectrum.zeroLocus (a : Set S.A) ∩
      PrimeSpectrum.zeroLocus (S.I : Set S.A))) δmax)
    (hmin : IsLeast (δ '' (PrimeSpectrum.zeroLocus (a : Set S.A) ∩
      PrimeSpectrum.zeroLocus (S.I : Set S.A))) δmin)
    (h5 : ∀ p : PrimeSpectrum S.A,
      p ∉ PrimeSpectrum.zeroLocus (S.I : Set S.A) →
      p ∉ associatedSubset S.I a →
      ((PrimeSpectrum.zeroLocus (p.asIdeal : Set S.A) ∩
        PrimeSpectrum.zeroLocus (a : Set S.A)) ∩
        PrimeSpectrum.zeroLocus (S.I : Set S.A)).Nonempty →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl S.M)) < (S.s : EInt) →
      (krullDimToEInt (Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule p.asIdeal.primeCompl S.M)) < ((S.s + 2 : ℤ) : EInt) ∨
        (S.d + δmax - 1 < δ p) ∨
        (∀ q : PrimeSpectrum S.A,
          q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set S.A) ∩
            PrimeSpectrum.zeroLocus (a : Set S.A)) ∩
            PrimeSpectrum.zeroLocus (S.I : Set S.A) →
          enatToEInt
              (Module.depth (Localization.AtPrime p.asIdeal)
                (maximalIdeal (Localization.AtPrime p.asIdeal))
                (LocalizedModule p.asIdeal.primeCompl S.M)) +
              krullDimToEInt
                (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
                  p.asIdeal.map (algebraMap S.A (Localization.AtPrime q.asIdeal)))) >
            ((S.d + S.s + δmax - δmin - 2 : ℤ) : EInt)))) :
    ∃ omega : DerivedCategory (ModuleCat.{max u w} S.A),
      AlgebraizationHypotheses (M := S.M) S.I a S.s S.d omega δ δmax δmin := by
  obtain ⟨omega, homega⟩ := S.dualizing
  refine ⟨omega, hcomplete, homega, S.cohomologicalDimension_le, ?_, hδ, hmax, hmin, h5⟩
  exact fun p hp _ ↦ or_iff_not_imp_left.2 fun hdep q hq ↦
    (depth_or_depth_add_dimension_of_mem_zeroLocus S a haT p q hq.1.1 hp hq.1.2).resolve_left hdep

/-! ### Parts (C) and (D): the local case at `𝔞 = 𝔪` -/

section Local

variable (S : BootstrapSituation.{u, u, w}) [IsLocalRing S.A]

/-- When the closed point lies in `T`, the ideal `I` of the situation is proper: the closed point
lies on `V(I)`. -/
private theorem ne_top_of_closedPoint_mem (hmT : closedPoint S.A ∈ S.T) : S.I ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal S.A).ne_top (S.subset_adicLocus hmT)

/-- The zero locus of the maximal ideal of a local ring is the closed point, so it is contained
in `T` as soon as the closed point belongs to `T`. -/
private theorem zeroLocus_maximalIdeal_subset (hmT : closedPoint S.A ∈ S.T) :
    PrimeSpectrum.zeroLocus ((maximalIdeal S.A : Ideal S.A) : Set S.A) ⊆ S.T := by
  rw [PrimeSpectrum.zeroLocus_eq_singleton (maximalIdeal S.A)]
  exact Set.singleton_subset_iff.2 hmT

/-- **Stacks Project, Tag 0EFV, part (C).** Let `S` be a bootstrap situation whose ring is local
with maximal ideal `𝔪`, and suppose `𝔪 ∈ T`, which is the standing hypothesis `V(𝔞) ⊆ T` at
`𝔞 = 𝔪`. Then all hypotheses of Stacks 0DXM and of Stacks 0EFQ hold for `A, 𝔪, I, M`.

This is part (A) at `𝔞 = 𝔪`: in a local ring the Jacobson radical is the maximal ideal, which
contains `I` because the closed point lies in `T ⊆ V(I)`. The hypotheses of Stacks 0DXM are
those of Stacks 0EFI at `J = 𝔪` by `localStabilizationHypotheses_iff`, and hypothesis (6) of
Stacks 0EFQ is hypothesis (6) of Stacks 0EFK there by
`depthGtOnAssociatedSubset_maximalIdeal_iff`. -/
@[stacks 0EFV "part (C): all hypotheses of Stacks 0DXM and Stacks 0EFQ for A, 𝔪, I, M"]
public theorem localStabilizationHypotheses_and_depthGtAtMaximalIdeal_of_mem
    (hmT : closedPoint S.A ∈ S.T) :
    (∃ omega : DerivedCategory (ModuleCat.{max u w} S.A),
        LocalStabilizationHypotheses (M := S.M) S.I S.s S.d omega) ∧
      DepthGtAtMaximalIdeal (M := S.M) S.I S.s := by
  have hItop : S.I ≠ ⊤ := ne_top_of_closedPoint_mem S hmT
  have hIm : S.I ≤ maximalIdeal S.A := S.subset_adicLocus hmT
  obtain ⟨⟨omega, homega⟩, h6⟩ := stabilizationHypotheses_and_depthGtOnAssociatedSubset S
    (maximalIdeal S.A) hIm (zeroLocus_maximalIdeal_subset S hmT)
    (hIm.trans_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
  exact ⟨⟨omega, (localStabilizationHypotheses_iff S.I S.s S.d omega).2 ⟨hItop, homega⟩⟩,
    (depthGtOnAssociatedSubset_maximalIdeal_iff hItop S.s).1 h6⟩

/-- **Stacks Project, Tag 0EFV, part (D).** Let `S` be a bootstrap situation whose ring is local
with maximal ideal `𝔪` and `I`-adically complete, and suppose `𝔪 ∈ T`, which is the standing
hypothesis `V(𝔞) ⊆ T` at `𝔞 = 𝔪`. Then all hypotheses of Stacks 0DXP hold for `A, 𝔪, I, M`.

Conditions (1) and (2) are the completeness together with assumption (1) of the situation,
condition (3) is assumption (3) of the situation, and condition (4) is the same as condition (4)
of Stacks 0DXM, proved in part (C). -/
@[stacks 0EFV "part (D): all hypotheses of Stacks 0DXP for A, 𝔪, I, M"]
public theorem localAlgebraizationHypotheses_of_mem
    (hcomplete : IsAdicComplete S.I S.A) (hmT : closedPoint S.A ∈ S.T) :
    ∃ omega : DerivedCategory (ModuleCat.{max u w} S.A),
      LocalAlgebraizationHypotheses (M := S.M) S.I S.s S.d omega := by
  obtain ⟨⟨omega, H⟩, -⟩ :=
    localStabilizationHypotheses_and_depthGtAtMaximalIdeal_of_mem S hmT
  exact ⟨omega, H.ne_top, hcomplete, H.dualizing, S.cohomologicalDimension_le,
    H.depthOrDimensionBound⟩

end Local

end Stacks.Algebraization

end
