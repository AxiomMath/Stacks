module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BoundaryDepthOne
public import StacksFrontier.AlgebraicGeometry.Algebraization.BoundaryFlag
public import StacksFrontier.AlgebraicGeometry.Algebraization.BoundaryQuotientHeight
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction

/-!
# Positive depth at an immediate specialization leaving the depth-two locus

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`, let `A` be `I`-adically complete with a dualizing
complex and `cd(A, I) ≤ d` for some `d ≥ 1`, and let `ℱ` be a coherent `𝒪_U`-module whose
completion satisfies the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3]. Let
`x ⤳ x'` be an immediate specialization in `U` with `x'` in the depth-two locus
`T = {x ∈ U | \overline{\{x\}} ∩ Y ⊆ Z}` and `x` outside it. Then `depth(ℱ_x) ≥ 1`.

This is the whole content of the proof of [Stacks, Tag 0EJ8] apart from its appeals to
[Stacks, Tag 0EI3] and [Stacks, Tag 0EJ7]: it is exactly the depth hypothesis that the existence
half of [Stacks, Tag 0EI3] consumes along `T`.

## Main results

* `Stacks.Algebraization.exists_distanceToZ_eq_one_specializes_of_no_component` — the geometric
  half of the second case: when no irreducible component of `\overline{\{x\}} ∩ Y` lies in `Z`,
  the boundary flag produces a point of `U` below `x`, at distance one from `Z`, of codimension
  at most `d` in `\overline{\{x\}}`.
* `Stacks.Algebraization.one_le_depth_stalk_of_isImmediateSpecialization_notMem_depthTwoLocus` —
  the depth bound, by a case split on whether some component lies in `Z`.

## Implementation notes

The source splits on whether `\overline{\{x\}} ∩ Y` has an irreducible component contained in
`Z`. In the first case the components lie on both sides of `Z` and [Stacks, Tag 0EJ5] applies,
which is `Stacks.Algebraization.one_le_depth_stalk_of_component_subset_Z`. In the second case
`Stacks.Algebraization.exists_boundary_flag_of_no_component` produces a point `z` of `Y` minimal
over `𝔭_{x'} + I` and lying in `Z`, together with an immediate generalization `y` of `z` inside
`Y` but outside `Z`; then `δ^Y_Z(y) = 1`, and the dimension bookkeeping of
`Stacks.Algebraization.quotient_height_le_cohomologicalDimension` — which is where
[Stacks, Tag 0DXF] and the catenary hypothesis enter — bounds the codimension of `y` in
`\overline{\{x\}}` by `cd(A, I) ≤ d`. Both cases end in
`Stacks.Algebraization.one_le_depth_stalk_of_specializes_of_distanceToZ_eq_one`.

The first case uses [Stacks, Tag 0EJ5], and through it [Stacks, Tag 0EG5] with the comparison of
[Stacks, Tag 0EIF], `Stacks.Algebraization.serreOneAlternativeComparison`; nothing is assumed
beyond the hypotheses stated.

## References

* [Stacks Project, Tag 0EJ8](https://stacks.math.columbia.edu/tag/0EJ8)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3)
* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5)
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
* [Stacks Project, Tag 02IM](https://stacks.math.columbia.edu/tag/02IM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- Membership of the depth-two locus, read on primes: every prime above `𝔭_{x'}` which
contains `I` contains `𝔞`. -/
public theorem le_asIdeal_of_mem_depthTwoLocus (S : AlgebraizationSituation.{u})
    {x' : S.U.toScheme} (hx' : x' ∈ depthTwoLocus S) (r : PrimeSpectrum S.A)
    (hr : (S.U.ι.base x').asIdeal ≤ r.asIdeal) (hIr : S.I ≤ r.asIdeal) :
    S.a ≤ r.asIdeal := by
  have hYr : r ∈ Set.range S.Yι.base := by
    rw [range_Yι_base]
    exact hIr
  have hZr : r ∈ Set.range S.Zι.base :=
    hx' ⟨(PrimeSpectrum.le_iff_mem_closure (S.U.ι.base x' : PrimeSpectrum S.A) r).mp hr, hYr⟩
  rw [range_Zι_base] at hZr
  exact hZr

/-- The underlying prime of a point of `U` is below that of a specialization of it. -/
public theorem asIdeal_le_asIdeal_of_specializes (S : AlgebraizationSituation.{u})
    {x x' : S.U.toScheme} (hxx' : x ⤳ x') :
    (S.U.ι.base x).asIdeal ≤ (S.U.ι.base x').asIdeal :=
  (PrimeSpectrum.le_iff_specializes (S.U.ι.base x : PrimeSpectrum S.A) (S.U.ι.base x')).mpr
    (hxx'.map S.U.ι.continuous)

/-- An injective continuous map to `Spec A` sends an immediate specialization to a strict
inequality of primes. -/
private theorem lt_of_isImmediateSpecialization {R X : Type*} [CommRing R] [TopologicalSpace X]
    {f : X → PrimeSpectrum R} (hf : Continuous f) (hinj : Function.Injective f) {x x' : X}
    (h : IsImmediateSpecialization x x') : f x < f x' :=
  lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).mpr (h.1.map hf))
    fun e => h.2.1 (hinj e)

/-- An immediate specialization in the open `U` is a covering relation between the underlying
primes of `A`: the open immersion carries the immediate specialization to `X`, and nothing can
sit strictly between the two primes. -/
public theorem covBy_of_isImmediateSpecialization (S : AlgebraizationSituation.{u})
    {x x' : S.U.toScheme} (himm : IsImmediateSpecialization x x') :
    CovBy (α := PrimeSpectrum S.A) (S.U.ι.base x) (S.U.ι.base x') := by
  have himmX : IsImmediateSpecialization (S.U.ι.base x) (S.U.ι.base x') :=
    himm.map_of_isOpenEmbedding S.U.ι.isOpenEmbedding
  refine ⟨lt_of_isImmediateSpecialization S.U.ι.continuous S.U.ι.isOpenEmbedding.injective himm,
    ?_⟩
  intro t ht htx'
  rcases himmX.2.2 t
    ((PrimeSpectrum.le_iff_specializes (S.U.ι.base x : PrimeSpectrum S.A) t).mp ht.le)
    ((PrimeSpectrum.le_iff_specializes t (S.U.ι.base x' : PrimeSpectrum S.A)).mp htx'.le) with
    h | h
  · exact ht.ne h.symm
  · exact htx'.ne h

/-- **The geometric half of the second case of [Stacks, Tag 0EJ8].** Let `A` be `I`-adically
complete and universally catenary with `cd(A, I) ≤ d`, let `x ⤳ x'` be an immediate
specialization in `U` with `x'` in the depth-two locus, and suppose no irreducible component of
the closed fibre `\overline{\{x\}} ∩ Y` is contained in `Z`. Then there is a point `y` of `U`
with `x ⤳ y`, lying over a point `r` of `Y` at distance exactly `1` from `Z`, whose codimension
in `\overline{\{x\}}` is at most `d`.

The boundary flag of `Stacks.Algebraization.exists_boundary_flag_of_no_component` supplies `z`
and `y`; the distance is exactly one because `z ∈ Z`, `y ∉ Z` and `z` is an immediate
specialization of `y`; and the codimension bound is
`Stacks.Algebraization.quotient_height_le_cohomologicalDimension` applied to the covering
relation `𝔭_x ⋖ 𝔭_{x'}`. -/
public theorem exists_distanceToZ_eq_one_specializes_of_no_component
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (hcat : Ring.IsUniversallyCatenary S.A) (d : ℤ)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      S.I.fg_of_isNoetherianRing ≤ d)
    (x x' : S.U.toScheme) (himm : IsImmediateSpecialization x x')
    (hx' : x' ∈ depthTwoLocus S)
    (hcomponent : ¬ ∃ C : Set (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)),
      C ∈ irreducibleComponents (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) ∧
        C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}) :
    ∃ (y : S.U.toScheme) (r : S.Y),
      S.U.ι.base y = S.Yι.base r ∧
      S.distanceToZ r = 1 ∧
      x ⤳ y ∧
      Ideal.height ((S.U.ι.base y).asIdeal.map
        (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)) ≤ (d.toNat : ℕ∞) := by
  classical
  have hcov := covBy_of_isImmediateSpecialization S himm
  obtain ⟨z, r, hzmin, hzZ, hry, hrZ, hrimm⟩ :=
    exists_boundary_flag_of_no_component S (S.U.ι.base x) (S.U.ι.base x') hcov.le
      (le_asIdeal_of_mem_depthTwoLocus S hx') hcomponent
  -- `r` lies outside `Z`, hence inside `U`.
  have hrU : S.Yι.base r ∈ S.U := by
    have hnot : S.Yι.base r ∉ Set.range S.Zι.base := fun hmem =>
      hrZ ((mem_closedSubsetZ_iff_mem_range_Zι S r).mpr hmem)
    rw [range_Zι_base] at hnot
    exact hnot
  -- The distance of `r` from `Z` is exactly one.
  have hfin : Algebra.FiniteType S.A (S.A ⧸ S.I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ S.A S.I) Ideal.Quotient.mk_surjective
  have hdist : S.distanceToZ r = 1 :=
    distanceFunction_eq_one_of_isImmediateSpecialization_of_notMem S.Y S.closedSubsetZ
      (isCatenarySpace_of_isCatenary (hcat (S.A ⧸ S.I))) hrimm hzZ hrZ
  -- The codimension bound, from the dimension bookkeeping.
  have hheight := quotient_height_le_cohomologicalDimension hcat S.I (S.U.ι.base x)
    (S.U.ι.base x') (S.Yι.base r) (S.Yι.base z) hcov hry
    (lt_of_isImmediateSpecialization S.Yι.continuous S.Yι.isClosedEmbedding.injective hrimm)
    hzmin
  have hprimeR : (S.Yι.base r).asIdeal.IsPrime := (S.Yι.base r).isPrime
  have hle : ((S.Yι.base r).asIdeal.map
      (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)).height ≤ (d.toNat : ℕ∞) := by
    have hprime : ((S.Yι.base r).asIdeal.map
        (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hry
    rw [← ENat.natCast_toNat (Ideal.height_ne_top hprime.ne_top)]
    exact Nat.cast_le.mpr (by omega)
  exact ⟨⟨S.Yι.base r, hrU⟩, r, rfl, hdist,
    S.U.ι.isOpenEmbedding.isEmbedding.specializes_iff.mp
      ((PrimeSpectrum.le_iff_specializes (S.U.ι.base x : PrimeSpectrum S.A)
        (S.Yι.base r)).mp hry), hle⟩

/-- **The depth bound of [Stacks, Tag 0EJ8] along the depth-two locus.** In an algebraization
situation with `A` `I`-adically complete, carrying a dualizing complex, and with
`cd(A, I) ≤ d` for some `d ≥ 1`, let `ℱ` be a coherent `𝒪_U`-module whose completion satisfies
the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3]. If `x ⤳ x'` is an immediate
specialization in `U` with `x'` in the depth-two locus and `x` outside it, then

  `depth(ℱ_x) ≥ 1`.

If some irreducible component of `\overline{\{x\}} ∩ Y` lies in `Z` the components lie on both
sides of `Z` and this is [Stacks, Tag 0EJ5]; otherwise the boundary flag gives a point of `U`
below `x` at distance one from `Z` and of codimension at most `d`, and the strict inequalities
force the depth there. -/
public theorem one_le_depth_stalk_of_isImmediateSpecialization_notMem_depthTwoLocus
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      S.I.fg_of_isNoetherianRing ≤ d)
    (hstrict : SatisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) 1 (1 + d))
    (x x' : S.U.toScheme) (himm : IsImmediateSpecialization x x')
    (hx' : x' ∈ depthTwoLocus S) (hx : x ∉ depthTwoLocus S) :
    1 ≤ Module.depth (S.U.toScheme.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk x))
      ((stalkModuleFunctor x).obj F.obj) := by
  classical
  by_cases hcomponent : ∃ C : Set (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)),
      C ∈ irreducibleComponents (S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) ∧
        C ⊆ {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}
  · exact one_le_depth_stalk_of_component_subset_Z S F d hd K hK hcd hstrict x hx
      hcomponent
  · have hcat := Dualizing.isUniversallyCatenary_of_isDualizingComplex hK
    obtain ⟨y, r, hyr, hdist, hxy, hheight⟩ :=
      exists_distanceToZ_eq_one_specializes_of_no_component S hcat d hcd x x' himm hx'
        hcomponent
    have hInotp : ¬ S.I ≤ (S.U.ι.base x).asIdeal := fun hI =>
      x'.property (le_asIdeal_of_mem_depthTwoLocus S hx' (S.U.ι.base x') le_rfl
        (hI.trans (asIdeal_le_asIdeal_of_specializes S himm.1)))
    exact one_le_depth_stalk_of_specializes_of_distanceToZ_eq_one S F d (by omega) hcat hstrict
      x y hxy r hyr hdist hInotp hheight

end Stacks.Algebraization

end
