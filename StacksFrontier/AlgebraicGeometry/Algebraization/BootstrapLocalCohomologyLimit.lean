module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapCompletionLocal
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapDepth
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparisonLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdealCollapse
public import StacksFrontier.RingTheory.LocalCohomology.CompletedLimitComparison

/-!
# Local cohomology as the limit of the local cohomologies of the adic quotients

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M` a finite `A`-module, and let `J` and `J'`
be ideals with `V(J') ∩ V(I) = V(J) ∩ V(I)`. Composing the arrow `RΓ_{J'}(M) ⟶ RΓ_J(M)^∧` of
Stacks 0EFL with the Milnor comparison of Stacks 0EEW gives a canonical map

`Hⁱ_{J'}(M) ⟶ lim Hⁱ_J(M/IⁿM)`,

and this file proves that it is an isomorphism in two cases.

Stacks 0EFR is the local case `J = J' = 𝔪`: in the bootstrap situation of Stacks 0EFU with `A`
local and `T = {𝔪}`, the map `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is an isomorphism for `i ≤ s` and
these modules are annihilated by a power of `I`. Stacks 0EG0 is the case `J = 𝔞` of an ideal
`I ⊆ 𝔞 ⊆ A` with `T = V(𝔞)`, in the single degree `s + 1`: there is an ideal `J₀ ⊆ 𝔞` with
`V(J₀) ∩ V(I) = V(𝔞)` such that `H^{s+1}_J(M) ⟶ lim H^{s+1}_𝔞(M/IⁿM)` is an isomorphism for
every `J ⊆ J₀` with `V(J) ∩ V(I) = V(𝔞)`. Here it is proved for `𝔞` the maximal ideal of a
Noetherian local ring.

## Main definitions

* `Stacks.Algebraization.localCohomologyToAdicQuotientLimit`: the canonical map
  `Hⁱ_{J'}(M) ⟶ lim Hⁱ_J(M/IⁿM)`.

## Main results

* `Stacks.Algebraization.localStabilizationHypotheses_and_depthGtAtMaximalIdeal`: in the
  bootstrap situation with `A` local and `T = {𝔪}`, the hypotheses of Stacks 0DXM and hypothesis
  (6) of Stacks 0EFQ hold for `A, I, 𝔪, M`.
* `Stacks.Algebraization.exists_pow_le_annihilator_localCohomologyModule_of_eq_closedPoint`: a
  single power of `I` annihilates `Hⁱ_𝔪(M)` for all `i ≤ s`.
* `Stacks.Algebraization.isIso_homology_localCohomologyToCompletedLocalCohomology_maximalIdeal`:
  for `I`-adically complete `A`, the map `RΓ_𝔪(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism on cohomology
  in degrees `i ≤ s`.
* `Stacks.Algebraization.isIso_localCohomologyToAdicQuotientLimit_and_exists_pow_le_annihilator`:
  if `RΓ_𝔪(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism on cohomology in degrees `i ≤ s`, then
  `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is an isomorphism for `i ≤ s` and a power of `I` annihilates
  these modules.
* `Stacks.Algebraization.isIso_localCohomologyToAdicQuotientLimit_of_isAdicComplete`: the same
  two assertions for `I`-adically complete `A`.
* `Stacks.Algebraization.isIso_homology_localCohomologyToCompletedLocalCohomology_adicCompletion`:
  `RΓ_{𝔪'}(M') ⟶ RΓ_{𝔪'}(M')^∧` is an isomorphism on cohomology in degrees `i ≤ s` over the
  `I`-adic completion `A'`, for arbitrary `A`.
* `Stacks.Algebraization.isIso_localCohomologyToAdicQuotientLimit_adicCompletion`: the two
  assertions over the `I`-adic completion `A', I', M'`, for arbitrary `A`.
* `Stacks.Algebraization.exists_ideal_isIso_localCohomologyToAdicQuotientLimit`: the assertion of
  Stacks 0EG0 for `𝔞` the maximal ideal of a Noetherian local ring.

## References

* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0EG0](https://stacks.math.columbia.edu/tag/0EG0)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
* [Stacks Project, Tag 0EID](https://stacks.math.columbia.edu/tag/0EID)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0EFQ](https://stacks.math.columbia.edu/tag/0EFQ)
* [Stacks Project, Tag 0DXM](https://stacks.math.columbia.edu/tag/0DXM)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
* [Stacks Project, Tag 0DXF](https://stacks.math.columbia.edu/tag/0DXF)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 0925](https://stacks.math.columbia.edu/tag/0925)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-! ### The canonical map to the limit -/

section Map

variable (A : Type u) [CommRing A] [IsNoetherianRing A]

/-- For ideals `I`, `J` and `J'` of a Noetherian ring with `V(J') ∩ V(I) = V(J) ∩ V(I)` and a
finite module `M`, the canonical map

`Hⁱ_{J'}(M) ⟶ lim Hⁱ_J(M/IⁿM)`:

the degree-`i` cohomology of the arrow `RΓ_{J'}(M) ⟶ RΓ_J(M)^∧` of Stacks 0EFL, namely
`Stacks.Algebraization.localCohomologyToCompletedLocalCohomology`, followed by the comparison
map of Stacks 0EEW out of the cohomology of the derived limit `RΓ_J(M)^∧` of the tower
`n ↦ RΓ_J(M/IⁿM)`. -/
public def localCohomologyToAdicQuotientLimit (I J J' : Ideal A) (M : ModuleCat.{u} A)
    [Module.Finite A M]
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) (i : ℤ) :
    Stacks.LocalCohomology.localCohomologyModule A J' J'.fg_of_isNoetherianRing M i ⟶
      limit (Dualizing.adicQuotientLocalCohomologySystem A I J J.fg_of_isNoetherianRing M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyToCompletedLocalCohomology A I J J' I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing M hV) ≫
    Dualizing.completedLocalCohomologyToLimit A I J J.fg_of_isNoetherianRing M
      (Dualizing.completedLocalCohomology A I J I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing M)
      (Dualizing.isDerivedLimit_completedLocalCohomology A I J I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing M) i

end Map

/-! ### Stacks 0EFR: the local case at the closed point -/

section Local

/-- A value of `WithBot ℕ∞` that is neither `⊥` nor `⊤` is a natural number. -/
private theorem exists_natCast_of_ne_bot_of_lt_top {x : WithBot ℕ∞} (hbot : x ≠ ⊥)
    (htop : x < ⊤) : ∃ n : ℕ, x = ((n : ℕ) : WithBot ℕ∞) := by
  lift x to ℕ∞ using hbot
  lift x to ℕ using fun h ↦ htop.ne (by rw [h]; rfl)
  exact ⟨x, rfl⟩

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- For a prime `𝔭` of a Noetherian local ring with `V(𝔭) ∩ V(I) = {𝔪}`, the bound
`cd(A, I) ≤ d` gives `dim(A/𝔭) ≤ d`. -/
private theorem krullDimToEInt_quotient_le (I : Ideal A) (d : ℤ)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (p : PrimeSpectrum A)
    (hV : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) = {closedPoint A}) :
    krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal)) ≤ (d : EInt) := by
  have hnt : Nontrivial (A ⧸ p.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr p.2.ne_top
  have hlt : ringKrullDim (A ⧸ p.asIdeal) < ⊤ :=
    (ringKrullDim_quotient_le p.asIdeal).trans_lt (ringKrullDim_lt_top (R := A))
  have hbot : ringKrullDim (A ⧸ p.asIdeal) ≠ ⊥ := Order.bot_lt_krullDim.ne'
  obtain ⟨n, hn⟩ := exists_natCast_of_ne_bot_of_lt_top hbot hlt
  rw [hn, krullDimToEInt_natCast]
  exact WithBotTop.coe_le_coe.mpr
    ((Stacks.LocalCohomology.ringKrullDim_quotient_le_cohomologicalDimension' A p.asIdeal I
      I.fg_of_isNoetherianRing hV n hn).trans hcd)

variable (S : BootstrapSituation.{u, u, u})

/-- In the bootstrap situation with `T = {𝔪}` the ideal `I` is contained in the maximal
ideal. -/
private theorem le_maximalIdeal_of_eq_closedPoint [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) : S.I ≤ maximalIdeal S.A :=
  S.subset_adicLocus (by rw [hT]; exact Set.mem_singleton _)

/-- In the bootstrap situation of Stacks 0EFU with `A` local and `T = {𝔪}`, the hypotheses
(1)–(4) of Stacks 0DXM and hypothesis (6) of Stacks 0EFQ hold for `A, I, 𝔪, M`, for every
dualizing complex `omega`. -/
@[stacks 0EFV "part (C) for T = {𝔪}: the hypotheses of Stacks 0DXM and hypothesis (6) of
Stacks 0EFQ, with the dualizing complex of Situation 0EFU supplied as the witness omega"]
public theorem localStabilizationHypotheses_and_depthGtAtMaximalIdeal [IsLocalRing S.A]
    (hT : S.T = {closedPoint S.A}) (omega : DerivedCategory (ModuleCat.{u} S.A))
    (homega : Dualizing.IsDualizingComplex omega) :
    LocalStabilizationHypotheses (M := S.M) S.I S.s S.d omega ∧
      DepthGtAtMaximalIdeal (M := S.M) S.I S.s := by
  have hclosed : closedPoint S.A ∈ S.T := by rw [hT]; exact Set.mem_singleton _
  have hItop : S.I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal S.A).ne_top (le_maximalIdeal_of_eq_closedPoint S hT)
  have hmemI : ∀ p : PrimeSpectrum S.A, closedPoint S.A ∈
      PrimeSpectrum.zeroLocus (p.asIdeal : Set S.A) ∩
        PrimeSpectrum.zeroLocus (S.I : Set S.A) := fun p ↦
    ⟨closedPoint_mem_zeroLocus p.2.ne_top, closedPoint_mem_zeroLocus hItop⟩
  have h6 : DepthGtAtMaximalIdeal (M := S.M) S.I S.s := by
    intro p hp hpV
    refine depth_localized_gt_of_no_intermediate_prime S p (closedPoint S.A)
      (IsLocalRing.le_maximalIdeal p.2.ne_top) hp hclosed ?_
    rintro ⟨r, hpr, -, hrI, hrT⟩
    have hmem : r ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set S.A) ∩
        PrimeSpectrum.zeroLocus (S.I : Set S.A) := ⟨hpr, hrI⟩
    rw [hpV, Set.mem_singleton_iff] at hmem
    exact hrT (hmem ▸ hclosed)
  refine ⟨⟨hItop, homega, ?_, ?_⟩, h6⟩
  · exact fun p _ hpV ↦ krullDimToEInt_quotient_le S.I S.d S.cohomologicalDimension_le p hpV
  · intro p hp hpV
    obtain ⟨r, hr, hrne⟩ : ∃ r : PrimeSpectrum S.A,
        r ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set S.A) ∩
          PrimeSpectrum.zeroLocus (S.I : Set S.A) ∧ r ≠ closedPoint S.A := by
      by_contra hcon
      push Not at hcon
      exact hpV (Set.Subset.antisymm (fun x hx ↦ hcon x hx) (Set.singleton_subset_iff.2
        (hmemI p)))
    have hrT : r ∉ S.T := by rw [hT]; simpa only [Set.mem_singleton_iff] using hrne
    have hbound := S.depth_or_depth_add_dimension p r (closedPoint S.A) hr.1
      (IsLocalRing.le_maximalIdeal r.2.ne_top) hp hr.2 hrT hclosed
    rwa [ringKrullDim_localization_quotient_map_of_eq_closedPoint
      (q := closedPoint S.A) rfl] at hbound

/-- In the bootstrap situation of Stacks 0EFU with `A` local and `T = {𝔪}`, a single power of
`I` annihilates `Hⁱ_𝔪(M)` in every degree `i ≤ s`. -/
@[stacks 0EFR "the annihilation assertion: Hⁱ_𝔪(M) is annihilated by a power of I for i ≤ s"]
public theorem exists_pow_le_annihilator_localCohomologyModule_of_eq_closedPoint
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) :
    ∃ n : ℕ, ∀ i : ℤ, i ≤ S.s →
      S.I ^ n ≤ Module.annihilator S.A
        (Stacks.LocalCohomology.localCohomologyModule S.A (maximalIdeal S.A)
          (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i) := by
  rcases lt_or_ge S.s 0 with hs | hs
  · refine ⟨0, fun i hi a _ ↦ ?_⟩
    have hzero := Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg S.A
      (maximalIdeal S.A) (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i
      (lt_of_le_of_lt hi hs)
    have : Subsingleton (Stacks.LocalCohomology.localCohomologyModule S.A (maximalIdeal S.A)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero
    exact Module.mem_annihilator.2 fun x ↦ Subsingleton.elim _ _
  obtain ⟨omega, homega⟩ := S.dualizing
  obtain ⟨H, h6⟩ := localStabilizationHypotheses_and_depthGtAtMaximalIdeal S hT omega homega
  have hItop : S.I ≠ ⊤ := H.ne_top
  have hd : (0 : ℤ) ≤ S.d :=
    (nonneg_cohomologicalDimension_of_mem_zeroLocus S.I (closedPoint S.A)
      (closedPoint_mem_zeroLocus hItop)).trans S.cohomologicalDimension_le
  obtain ⟨n, hn⟩ := exists_pow_le_annihilator_localCohomologyModule_maximalIdeal
    S.I S.s S.d omega H h6 hs hd
  exact ⟨n, fun i hi ↦ hn (maximalIdeal S.A) (zeroLocus_maximalIdeal_inter hItop) i hi⟩

/-- Precomposing with the forward map of an isomorphism does not change whether `F.map` of a
morphism is invertible. -/
private theorem isIso_map_comp_hom_iff {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Y) (e : Y ≅ Z) : IsIso (F.map (f ≫ e.hom)) ↔ IsIso (F.map f) := by
  rw [F.map_comp]
  have := (F.mapIso e).isIso_hom
  exact isIso_comp_right_iff _ _

/-- For `η : 𝟭 C ⟶ T` and `g : X ⟶ Y`, if `H.map g`, `H.map (T.map g)` and `H.map (η.app Y)` are
isomorphisms, then so is `H.map (η.app X)`. -/
private theorem isIso_map_unit_of_naturality_source
    {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) (T : C ⥤ C) (η : 𝟭 C ⟶ T) {X Y : C} (g : X ⟶ Y)
    (hg : IsIso (H.map g)) (hTg : IsIso (H.map (T.map g))) (hY : IsIso (H.map (η.app Y))) :
    IsIso (H.map (η.app X)) := by
  have := hg
  have := hTg
  have := hY
  have h : H.map g ≫ H.map (η.app Y) = H.map (η.app X) ≫ H.map (T.map g) := by
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map (η.naturality g)
  have : IsIso (H.map (η.app X) ≫ H.map (T.map g)) := by rw [← h]; infer_instance
  exact IsIso.of_isIso_comp_right (H.map (η.app X)) (H.map (T.map g))

/-- In the bootstrap situation with `A` local, `I`-adically complete and `T = {𝔪}`, the canonical
map `RΓ_𝔪(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism on cohomology in degrees `i ≤ s`. -/
public theorem isIso_homology_localCohomologyToCompletedLocalCohomology_maximalIdeal
    [IsLocalRing S.A] [IsAdicComplete S.I S.A] (hT : S.T = {closedPoint S.A})
    (i : ℤ) (hi : i ≤ S.s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i).map
      (localCohomologyToCompletedLocalCohomology S.A S.I (maximalIdeal S.A) (maximalIdeal S.A)
        S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) rfl)) := by
  obtain ⟨omega, homega⟩ := S.dualizing
  obtain ⟨H, h6⟩ := localStabilizationHypotheses_and_depthGtAtMaximalIdeal S hT omega homega
  have hItop : S.I ≠ ⊤ := H.ne_top
  have HL : LocalAlgebraizationHypotheses (M := S.M) S.I S.s S.d omega :=
    { ne_top := hItop
      adicComplete := inferInstance
      dualizing := homega
      cohomologicalDimension_le := S.cohomologicalDimension_le
      depthOrDimensionBound := H.depthOrDimensionBound }
  obtain ⟨J₀, hJ₀⟩ := exists_isLocalAlgebraizationIdeal S.I S.s S.d omega HL
  have hle : J₀ ≤ maximalIdeal S.A :=
    (le_maximalIdeal_of_zeroLocus_inter_eq_closedPoint hJ₀.zeroLocus_inter).1
  have hVmax : PrimeSpectrum.zeroLocus (J₀ : Set S.A) ∩
      PrimeSpectrum.zeroLocus (S.I : Set S.A) =
        PrimeSpectrum.zeroLocus ((maximalIdeal S.A : Ideal S.A) : Set S.A) ∩
          PrimeSpectrum.zeroLocus (S.I : Set S.A) :=
    zeroLocus_inter_eq_maximalIdeal_inter hItop hJ₀.zeroLocus_inter
  have hgiso := isIso_homologyMap_localCohomologyComparison_maximalIdeal S.I J₀ S.s h6
    hJ₀.zeroLocus_inter i hi
  have := isIso_completionFunctor_map_localCohomologyComparison S.I (maximalIdeal S.A) J₀
    S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
    (Ideal.fg_of_isNoetherianRing _) hle
    ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj (ModuleCat.of S.A S.M)) hVmax
  have hunitJ₀ := (isIso_map_comp_hom_iff
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i) _
    (completedLocalCohomologyShrinkIso S.A S.I (maximalIdeal S.A) J₀
      S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
      (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) hVmax)).mp
    (hJ₀.isIso J₀ le_rfl hJ₀.zeroLocus_inter i hi)
  have hunitmax := isIso_map_unit_of_naturality_source
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i)
    (adicCompletionFunctor S.A S.I S.I.fg_of_isNoetherianRing)
    (adicCompletionUnit S.A S.I S.I.fg_of_isNoetherianRing)
    (localCohomologyComparison S.A (maximalIdeal S.A) J₀
      (Ideal.fg_of_isNoetherianRing _) (Ideal.fg_of_isNoetherianRing _) hle
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj (ModuleCat.of S.A S.M)))
    hgiso inferInstance hunitJ₀
  exact (isIso_map_comp_hom_iff
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i) _
    (completedLocalCohomologyShrinkIso S.A S.I (maximalIdeal S.A) (maximalIdeal S.A)
      S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
      (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) rfl)).mpr hunitmax

/-- In Situation 0EFU with `A` local and `T = {𝔪}`, if `Hⁱ_𝔪(M) ⟶ Hⁱ(RΓ_𝔪(M)^∧)` is an
isomorphism for every `i ≤ s` (the hypothesis `hunit`), then `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is an
isomorphism for `i ≤ s` and a single power of `I` annihilates these modules. -/
public theorem isIso_localCohomologyToAdicQuotientLimit_and_exists_pow_le_annihilator
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A})
    (hunit : ∀ i : ℤ, i ≤ S.s →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i).map
        (localCohomologyToCompletedLocalCohomology S.A S.I (maximalIdeal S.A)
          (maximalIdeal S.A) S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
          (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) rfl))) :
    (∀ i : ℤ, i ≤ S.s →
        IsIso (localCohomologyToAdicQuotientLimit S.A S.I (maximalIdeal S.A)
          (maximalIdeal S.A) (ModuleCat.of S.A S.M) rfl i)) ∧
      ∃ n : ℕ, ∀ i : ℤ, i ≤ S.s →
        S.I ^ n ≤ Module.annihilator S.A
          (Stacks.LocalCohomology.localCohomologyModule S.A (maximalIdeal S.A)
            (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i) := by
  refine ⟨fun i hi ↦ ?_,
    exists_pow_le_annihilator_localCohomologyModule_of_eq_closedPoint S hT⟩
  exact IsIso.comp_isIso' (hunit i hi)
    (Stacks.LocalCohomology.isIso_completedLocalCohomologyToLimit S.A S.I
      (ModuleCat.of S.A S.M) _
      (Dualizing.isDerivedLimit_completedLocalCohomology S.A S.I (maximalIdeal S.A)
        S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
        (ModuleCat.of S.A S.M)) i)

/-- In the bootstrap situation of Stacks 0EFU with `A` local, `I`-adically complete and
`T = {𝔪}`, the map `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is an isomorphism for `i ≤ s` and a single
power of `I` annihilates these modules. -/
@[stacks 0EFR "both assertions, with no carried hypothesis, for I-adically complete A"]
public theorem isIso_localCohomologyToAdicQuotientLimit_of_isAdicComplete
    [IsLocalRing S.A] [IsAdicComplete S.I S.A] (hT : S.T = {closedPoint S.A}) :
    (∀ i : ℤ, i ≤ S.s →
        IsIso (localCohomologyToAdicQuotientLimit S.A S.I (maximalIdeal S.A)
          (maximalIdeal S.A) (ModuleCat.of S.A S.M) rfl i)) ∧
      ∃ n : ℕ, ∀ i : ℤ, i ≤ S.s →
        S.I ^ n ≤ Module.annihilator S.A
          (Stacks.LocalCohomology.localCohomologyModule S.A (maximalIdeal S.A)
            (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i) :=
  isIso_localCohomologyToAdicQuotientLimit_and_exists_pow_le_annihilator S hT
    (isIso_homology_localCohomologyToCompletedLocalCohomology_maximalIdeal S hT)

/-- The `I`-adic completion `A'` of the ring of a bootstrap situation is `I'`-adically complete. -/
private theorem isAdicComplete_adicCompletion :
    IsAdicComplete S.adicCompletion.I S.adicCompletion.A :=
  (IsAdicComplete.map_algebraMap_iff (S := AdicCompletion S.I S.A) S.I
    (AdicCompletion S.I S.A)).mpr (AdicCompletion.isAdicComplete S.I.fg_of_isNoetherianRing)

/-- In the bootstrap situation with `A` local and `T = {𝔪}`, the canonical map
`RΓ_{𝔪'}(M') ⟶ RΓ_{𝔪'}(M')^∧` over the `I`-adic completion `A'` is an isomorphism on cohomology
in degrees `i ≤ s`, with no completeness assumption on `A`. -/
public theorem isIso_homology_localCohomologyToCompletedLocalCohomology_adicCompletion
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) :
    letI : IsLocalRing S.adicCompletion.A :=
      BootstrapSituation.isLocalRing_adicCompletion S hT
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.adicCompletion.A) i).map
      (localCohomologyToCompletedLocalCohomology S.adicCompletion.A
        S.adicCompletion.I (maximalIdeal S.adicCompletion.A)
        (maximalIdeal S.adicCompletion.A)
        S.adicCompletion.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
        (Ideal.fg_of_isNoetherianRing _)
        (ModuleCat.of S.adicCompletion.A S.adicCompletion.M) rfl)) := by
  let : IsLocalRing S.adicCompletion.A :=
    BootstrapSituation.isLocalRing_adicCompletion S hT
  have := isAdicComplete_adicCompletion S
  exact isIso_homology_localCohomologyToCompletedLocalCohomology_maximalIdeal
    S.adicCompletion (adicCompletionLocus_eq_closedPoint S hT) i hi

/-- In the bootstrap situation with `A` local and `T = {𝔪}`, over the `I`-adic completion
`A', I', M'`: the map `Hⁱ_{𝔪'}(M') ⟶ lim Hⁱ_{𝔪'}(M'/(I')ⁿM')` is an isomorphism for `i ≤ s`,
and a single power of `I'` annihilates these modules. Nothing is assumed about `A` beyond
Situation 0EFU and the locality of the locus. -/
@[stacks 0EFR "both assertions read over the I-adic completion A', I', M' of the situation, for
an arbitrary A: Hⁱ_{𝔪'}(M') → lim Hⁱ_{𝔪'}(M'/(I')ⁿM') is an isomorphism for i ≤ s and a power of
I' annihilates these modules. No completeness assumption on A; this is the statement the
source's proof establishes over the completion"]
public theorem isIso_localCohomologyToAdicQuotientLimit_adicCompletion
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) :
    letI : IsLocalRing S.adicCompletion.A :=
      BootstrapSituation.isLocalRing_adicCompletion S hT
    (∀ i : ℤ, i ≤ S.adicCompletion.s →
        IsIso (localCohomologyToAdicQuotientLimit S.adicCompletion.A S.adicCompletion.I
          (maximalIdeal S.adicCompletion.A) (maximalIdeal S.adicCompletion.A)
          (ModuleCat.of S.adicCompletion.A S.adicCompletion.M) rfl i)) ∧
      ∃ n : ℕ, ∀ i : ℤ, i ≤ S.adicCompletion.s →
        S.adicCompletion.I ^ n ≤ Module.annihilator S.adicCompletion.A
          (Stacks.LocalCohomology.localCohomologyModule S.adicCompletion.A
            (maximalIdeal S.adicCompletion.A) (Ideal.fg_of_isNoetherianRing _)
            (ModuleCat.of S.adicCompletion.A S.adicCompletion.M) i) := by
  let : IsLocalRing S.adicCompletion.A :=
    BootstrapSituation.isLocalRing_adicCompletion S hT
  have := isAdicComplete_adicCompletion S
  exact isIso_localCohomologyToAdicQuotientLimit_of_isAdicComplete S.adicCompletion
    (adicCompletionLocus_eq_closedPoint S hT)

end Local

/-! ### Stacks 0EG0: degree `s + 1` at the maximal ideal -/

section Global

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

omit [IsNoetherianRing A] in
/-- For `I ⊆ 𝔞`, `V(𝔞) ∩ V(I) = V(𝔞)`. -/
public theorem zeroLocus_inter_eq_self_of_le {I a : Ideal A} (hIa : I ≤ a) :
    PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) :=
  Set.inter_eq_left.mpr (PrimeSpectrum.zeroLocus_anti_mono_ideal hIa)

/-- Let `A` be a Noetherian local ring with maximal ideal `𝔪`, let `I ⊆ 𝔪` be an ideal, let `M`
be a finite `A`-module and let `s` and `d` be integers. Assume that `A, I, 𝔪, M` satisfy the
conditions of Stacks 0EFL for `s + 1` and `d` with `J = 𝔪`. Then there is an ideal `J₀ ⊆ 𝔪` with
`V(J₀) ∩ V(I) = V(𝔪)` such that for every ideal `J ⊆ J₀` with `V(J) ∩ V(I) = V(𝔪)` the map

`H^{s+1}_J(M) ⟶ lim H^{s+1}_𝔪(M/IⁿM)`

is an isomorphism. -/
@[stacks 0EG0 "for the maximal ideal of a Noetherian local ring: the tag's conclusion in full at
𝔞 = 𝔪 -- the same ideal J₀ ≤ 𝔪, the same locus condition V(J₀) ∩ V(I) = V(𝔪), the same ∀ J ≤ J₀
with V(J) ∩ V(I) = V(𝔪), the same degree s+1, IsIso -- with the source's condition (2) in full
as H. The statement has no support-ideal parameter: 𝔪 is substituted throughout. The source's
condition (1) is used only to obtain Mittag-Leffler-ness of {H^s_𝔞(M/IⁿM)} from 0EIE, which at
the maximal ideal follows from the finiteness of the M/IⁿM and the Artinianness of local
cohomology there, via
Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology, so (1) is
not needed. The general support ideal is not covered; it needs 0EIE, which the library has only
as consequences of its own essential-constancy assertion
(RingTheory/LocalCohomology/EssentiallyConstantConsequences.lean). The specialisation is not
vacuous: V(𝔪) is the closed point, and J ranges over the ideals with V(J) ∩ V(I) = {𝔪}, which
include ideals strictly inside 𝔪"]
public theorem exists_ideal_isIso_localCohomologyToAdicQuotientLimit [IsLocalRing A]
    (I : Ideal A) (hIa : I ≤ maximalIdeal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A)) (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ)
    (H : AlgebraizationHypotheses (M := M) I (maximalIdeal A) (s + 1) d omega δ δmax δmin) :
    ∃ J₀ : Ideal A, J₀ ≤ maximalIdeal A ∧
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ∧
      ∀ J : Ideal A, J ≤ J₀ →
        ∀ hJ : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A),
          IsIso (localCohomologyToAdicQuotientLimit A I (maximalIdeal A) J (ModuleCat.of A M)
            (hJ.trans (zeroLocus_inter_eq_self_of_le hIa).symm) (s + 1)) := by
  obtain ⟨J₀, hJ₀⟩ :=
    exists_isAlgebraizationIdeal I (maximalIdeal A) (s + 1) d omega δ δmax δmin H
  refine ⟨J₀, hJ₀.le, ?_, fun J hJle hJ ↦ ?_⟩
  · exact hJ₀.zeroLocus_inter.trans (zeroLocus_inter_eq_self_of_le hIa)
  · exact IsIso.comp_isIso'
      (hJ₀.isIso J hJle (hJ.trans (zeroLocus_inter_eq_self_of_le hIa).symm) (s + 1) le_rfl)
      (Stacks.LocalCohomology.isIso_completedLocalCohomologyToLimit_of_isMittagLeffler
        A I (maximalIdeal A) (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of A M) _
        (Dualizing.isDerivedLimit_completedLocalCohomology A I (maximalIdeal A)
          I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of A M)) (s + 1)
        (Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology
          A I (ModuleCat.of A M) (s + 1 - 1)))

end Global

end Stacks.Algebraization

end
