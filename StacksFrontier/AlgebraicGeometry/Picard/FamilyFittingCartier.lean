/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.RingTheory.Fitting.LocallyPrincipalCoker
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.OpenLocus
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic

/-!
# The Fitting ideal sheaf of `H¹` of a family of Euler characteristic zero is a divisor

Let `X` be a proper scheme over a field `k` covered by two affine opens, `T` an integral scheme
over `k` and `M` an invertible module on `X ×_k T` all of whose fibres have Euler
characteristic `h⁰ - h¹ = 0`. Then the Fitting ideal sheaf `Θ = Fit₀ R¹pr_* M` on `T` is an
effective Cartier divisor as soon as it is not the whole of `T`.

On an affine chart the two-term Čech differential has a finite projective model `K₀ ⟶ K₁` whose
ranks differ by the fibre Euler characteristic, so they agree; hence `Θ` is locally principal
(`Stacks.Fitting.exists_map_fittingIdeal_coker_eq_span`). A local generator is a nonzerodivisor:
the ring is a domain, and a zero generator would put a nonempty open of the irreducible `T` into
the support of `Θ`, hence all of `T`.

This is the theta divisor of the construction of the polarization used for [Stacks, Tag 03U1].

## Main results

* `Stacks.FamilyFitting.isEffectiveCartierDivisor_familyFitting`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.TwoAffineCech Stacks.FibreCohomology

universe u

namespace Stacks.FamilyFitting

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {T : Scheme.{u}} (tT : T ⟶ Spec (.of k))

omit [IsProper fX] in
/-- The base change of a chart is a cartesian square over the chart. -/
theorem isPullback_chartMap_snd {A : CommRingCat.{u}} (j : Spec A ⟶ T) :
    IsPullback (chartMap fX tT j) (pullback.snd fX (j ≫ tT)) (pullback.snd fX tT) j := by
  have hbig : IsPullback (chartMap fX tT j ≫ pullback.fst fX tT) (pullback.snd fX (j ≫ tT)) fX
      (j ≫ tT) := by
    rw [show chartMap fX tT j ≫ pullback.fst fX tT = pullback.fst fX (j ≫ tT) by
      simp only [chartMap, pullback.lift_fst, Category.comp_id]]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right hbig (by simp only [chartMap, pullback.lift_snd])
    (IsPullback.of_hasPullback fX tT)

include hU hUaff in
/-- **The theta divisor is an effective Cartier divisor.** For an invertible module `M` on
`X ×_k T` with `T` integral, all of whose fibres have Euler characteristic zero, the Fitting ideal
sheaf of `H¹` is an effective Cartier divisor as soon as its support is not all of `T`. -/
theorem isEffectiveCartierDivisor_familyFitting [IsIntegral T] (M : (pullback fX tT).Modules)
    [Stacks.Ample.IsInvertibleModule _ M]
    (hχ : ∀ t : T, Module.finrank (T.residueField t) (fibreCohomology (pullback.snd fX tT) M t 0) =
      Module.finrank (T.residueField t) (fibreCohomology (pullback.snd fX tT) M t 1))
    (hq : ∃ q : T, q ∉ (familyFitting fX U hU hUaff tT M).support) :
    Stacks.Divisors.IsEffectiveCartierDivisor (familyFitting fX U hU hUaff tT M) := by
  classical
  rw [Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor]
  intro x
  obtain ⟨_, ⟨V₀, hV₀', rfl⟩, hxV₀, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV₀ : IsAffineOpen V₀ := hV₀'
  let := chartAlgebra tT hV₀.fromSpec
  have hA := isPullback_chart fX tT hV₀.fromSpec
  have hsqT := isPullback_chartMap_snd fX tT hV₀.fromSpec
  have : IsSeparated (pullback.snd fX (hV₀.fromSpec ≫ tT)) :=
    isSeparated_of_isPullback' fX _ _ hA
  have : IsProper (pullback.snd fX (hV₀.fromSpec ≫ tT)) :=
    isProper_of_isPullback' fX _ _ hA
  have : IsProper (pullback.snd fX tT) := inferInstance
  have : ((Scheme.Modules.pullback (chartMap fX tT hV₀.fromSpec)).obj M).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have : M.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have := flat_cech_of_isPullback fX U hUaff _ _ hA
    ((Scheme.Modules.pullback (chartMap fX tT hV₀.fromSpec)).obj M) 1
  obtain ⟨K₀, K₁, _, _, _, _, _, _, _, _, δ, φ₀, φ₁, hsq⟩ :=
    hasFiniteProjectiveModel_of_isPullback fX U hU hUaff _ _ hA
      ((Scheme.Modules.pullback (chartMap fX tT hV₀.fromSpec)).obj M)
  have : Module.Finite Γ(T, V₀) ((Stacks.Cech.alternatingCechModuleComplex
      (pullback.snd fX (hV₀.fromSpec ≫ tT)) (sqCover U (pullback.fst fX (hV₀.fromSpec ≫ tT)))
      ((Scheme.Modules.pullback (chartMap fX tT hV₀.fromSpec)).obj M)).X 1 ⧸
      LinearMap.range (cechD (pullback.snd fX (hV₀.fromSpec ≫ tT))
        (sqCover U (pullback.fst fX (hV₀.fromSpec ≫ tT)))
        ((Scheme.Modules.pullback (chartMap fX tT hV₀.fromSpec)).obj M))) :=
    Module.Finite.equiv hsq.cokerEquiv
  -- the ideal on `V₀` is the Fitting ideal of `coker δ`
  have hI : (familyFitting fX U hU hUaff tT M).ideal ⟨V₀, hV₀⟩ =
      fittingIdeal (R := Γ(T, V₀)) (M := coker δ) ((0 : ℕ) : ℤ) := by
    rw [familyFitting_ideal, chartFitting, cechFitting, fittingCoker]
    exact (fittingIdeal_eq_of_linearEquiv hsq.cokerEquiv 0).symm
  -- the two terms of the model have the same rank: the fibres have Euler characteristic zero
  have hrank : ∀ q : PrimeSpectrum Γ(T, V₀), Module.rankAtStalk K₀ q = Module.rankAtStalk K₁ q := by
    intro q
    have h1 := Stacks.TwoTermComplex.finrank_ker_sub_finrank_coker δ q
    have hqb := hsq.baseChange q.asIdeal.ResidueField
    rw [hqb.kerEquiv.finrank_eq, hqb.cokerEquiv.finrank_eq,
      ← finrank_cohomologyOverField_zero_eq (pullback.snd fX (hV₀.fromSpec ≫ tT))
        (sqCover U (pullback.fst fX (hV₀.fromSpec ≫ tT))) _
        (iSup_sqCover U hU _) (isAffineOpen_sqCover fX U hUaff _ _ hA) q,
      ← finrank_cohomologyOverField_one_eq (pullback.snd fX (hV₀.fromSpec ≫ tT))
        (sqCover U (pullback.fst fX (hV₀.fromSpec ≫ tT))) _
        (iSup_sqCover U hU _) (isAffineOpen_sqCover fX U hUaff _ _ hA) q,
      finrank_fibre_eq_fibreCohomology, finrank_fibre_eq_fibreCohomology,
      finrank_fibreCohomology_eq_of_isPullback (pullback.snd fX tT) M _ _ _ hsqT _ (Iso.refl _) _ 0,
      finrank_fibreCohomology_eq_of_isPullback (pullback.snd fX tT) M _ _ _ hsqT _ (Iso.refl _) _ 1,
      hχ, sub_self] at h1
    omega
  -- the point `x` as a prime of the chart
  set p := hV₀.primeIdealOf ⟨x, hxV₀⟩
  obtain ⟨r, hr, a, ha⟩ := Stacks.Fitting.exists_map_fittingIdeal_coker_eq_span δ hrank p
  have hxr : x ∈ T.basicOpen r := by
    have h : (p : Spec Γ(T, V₀)) ∈ hV₀.fromSpec ⁻¹ᵁ T.basicOpen r := by
      rw [hV₀.fromSpec_preimage_basicOpen]; exact hr
    have h2 : hV₀.fromSpec p ∈ T.basicOpen r := h
    rwa [hV₀.fromSpec_primeIdealOf] at h2
  have := hV₀.isLocalization_basicOpen r
  have hD : (familyFitting fX U hU hUaff tT M).ideal (T.affineBasicOpen (U := ⟨V₀, hV₀⟩) r) =
      Ideal.span {algebraMap Γ(T, V₀) Γ(T, T.basicOpen r) a} := by
    rw [← (familyFitting fX U hU hUaff tT M).map_ideal_basicOpen ⟨V₀, hV₀⟩ r, hI]
    exact ha Γ(T, T.basicOpen r)
  refine ⟨T.affineBasicOpen (U := ⟨V₀, hV₀⟩) r, hxr,
    algebraMap Γ(T, V₀) Γ(T, T.basicOpen r) a, ?_, hD⟩
  have : Nonempty (T.affineBasicOpen (U := ⟨V₀, hV₀⟩) r).1 := ⟨⟨x, hxr⟩⟩
  have : IsDomain Γ(T, (T.affineBasicOpen (U := ⟨V₀, hV₀⟩) r).1) :=
    IsIntegral.component_integral _
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  obtain ⟨q, hq⟩ := hq
  apply hq
  -- a zero generator puts the nonempty open `D(r)` into the support of `Θ`
  have hsub : (T.basicOpen r : Set T) ⊆ (familyFitting fX U hU hUaff tT M).support := by
    intro y hy
    refine (Scheme.IdealSheafData.mem_support_iff_of_mem
      (U := T.affineBasicOpen (U := ⟨V₀, hV₀⟩) r) hy).2 ?_
    rw [hD, h0, Scheme.mem_zeroLocus_iff]
    intro f hf
    have hf' : f ∈ Ideal.span ({0} : Set Γ(T, (T.affineBasicOpen (U := ⟨V₀, hV₀⟩) r).1)) := hf
    rw [Ideal.mem_span_singleton, zero_dvd_iff] at hf'
    rw [hf', Scheme.basicOpen_zero]
    exact fun h => h
  have hdense : Dense (T.basicOpen r : Set T) :=
    (T.basicOpen r).isOpen.dense ⟨x, hxr⟩
  have hcl := (familyFitting fX U hU hUaff tT M).support.isClosed.closure_subset_iff.2 hsub
  exact hcl (hdense.closure_eq ▸ Set.mem_univ q)

end Stacks.FamilyFitting

end
