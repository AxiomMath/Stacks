module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexFittingIdeals
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexChartHomology
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.IntegralPerfectComplex
public import StacksFrontier.AlgebraicGeometry.IdealSheafLocallyFiniteProduct.Basic
public import StacksFrontier.Homology.Perfect.BoundedComplexCokernelRank
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransformFittingRank.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.PseudoMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Summands
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# The admissible blowup of Stacks 0ESQ

Let `X` be a scheme, `E ∈ D(𝒪_X)` perfect, and `U ⊆ X` a scheme-theoretically dense open on which
every `H^i(E)` is finite locally free of constant rank `r_i`. The blowup of `X` in the product of
the Fitting ideal sheaves `Fit_{i, k_i}(E)`, `k_i = r_{i+1} - r_{i+2} + ⋯`, is `U`-admissible, and
on it every `H^i` of the pullback of `E` is perfect of Tor dimension at most one.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.fittingIdealOfRanks`: the Fitting ideal sheaf
  `Fit_{i, k_i}(E)`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.fittingIdealProdOfRanks`: their product, a
  locally finite product.
* `AlgebraicGeometry.IsHomologyPerfectTorLEOne`: the `i`-th cohomology module of the derived
  pullback of `E` is perfect of Tor dimension at most one.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.fittingMinorIdeal_eq_top_and_eq_bot`:
  on a chart inside `U` the Fitting minor ideal at the index `k_i` is the unit ideal and the next
  one vanishes.
* `ComplexAndDivisorSituation.chartFittingIdeal_alternatingRankSum_sub_one_eq_bot`: the Fitting
  ideal sheaf just below the index vanishes on all of `X`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.locallyFinite_support_fittingIdealOfRanks`:
  locally on `X` almost all of the Fitting ideal sheaves are the unit ideal.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isAdmissibleBlowup_fittingIdealProdOfRanks` and
  `ComplexAndDivisorSituation.isEffectiveCartierDivisor_comap_fittingIdealOfRanks`: the blowup in
  the product is `U`-admissible and every `Fit_{i, k_i}(E)` becomes an effective Cartier divisor on
  it.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_and_hasTorAmplitude_homology_pullback`:
  on that blowup every cohomology sheaf of the pulled-back object is perfect of Tor dimension at
  most one.
* `AlgebraicGeometry.exists_admissibleBlowup_forall_isHomologyPerfectTorLEOne`: there is a
  `U`-admissible blowup after which every cohomology sheaf of the pullback of `E` is perfect of
  Tor dimension at most one.

## References

* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 0F7M](https://stacks.math.columbia.edu/tag/0F7M)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.FittingComplex

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- A zero module is finite locally free only of rank `0` over a nontrivial ring. -/
theorem Module.IsFiniteLocallyFreeOfRank.eq_zero_of_subsingleton {R : Type*} [CommRing R]
    [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M] [Subsingleton M] {r : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M r) : r = 0 := by
  have : Module.Finite R M := inferInstance
  obtain ⟨hbot, -⟩ := ((finiteLocallyFreeOfRank_fittingIdeal_tfae (R := R) (M := M) r).out 1 2).1 h
  by_contra hr
  have e : M ≃ₗ[R] (Fin 0 → R) := LinearEquiv.ofSubsingleton _ _
  have hfit := fittingIdeal_eq_of_linearEquiv e (r - 1)
  rw [fittingIdeal_fin_eq_bot_or_top, if_neg (by omega),
    show ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 by omega, hbot] at hfit
  exact bot_ne_top hfit

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable {X : Scheme.{u}} {E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
  (hE : IsPerfect.{u, u, u + 1} E)

/-- The affine charts of a perfect object cover the scheme. -/
theorem ofPerfect_cover (x : X) :
    ∃ C : AffineChart (ofPerfect X E hE), x ∈ (C.U : X.Opens) := by
  obtain ⟨C, hx, -⟩ := exists_affineChart_ofPerfect hE x ⊤ trivial
  exact ⟨C, hx⟩

section Rank

variable {U : X.Opens} {r : ℤ → ℕ}
  (hrank : ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} U.toScheme.toRingedSpace) i).obj
      ((derivedPullback U.ι.toLRSHom.toShHom).obj E)) (r i))

include hrank in
/-- On a chart inside the open of constant ranks, the chart complex has finite locally free
cohomology of those ranks. -/
theorem AffineChart.isFiniteLocallyFreeOfRank_homology (C : AffineChart (ofPerfect X E hE))
    (hCU : (C.U : X.Opens) ≤ U) (j : ℤ) :
    Module.IsFiniteLocallyFreeOfRank Γ(X, C.U)
      (C.complex.toCochainComplex.homology j) (r j) := by
  have h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).obj E)) (r j) :=
    Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso
      (homologyDerivedPullbackIsoRestrict X U j E) (hrank j)
  have h₂ := isFiniteLocallyFreeOfRank_restrict_of_le hCU _ h₁
  have h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((AffineChart.chartTilde C).obj
        ((HomologicalComplex.homologyFunctor (ModuleCat Γ(X, C.U)) (ComplexShape.up ℤ) j).obj
          C.complex.toCochainComplex)) (r j) :=
    Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso (AffineChart.chartHomologyIso C j) h₂
  have h₄ := Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_isIso C.U.2.isoSpec.hom
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ (r j)).2 h₃)
  exact (Stacks.Modules.tilde_isFiniteLocallyFreeOfRank_iff_module (R := Γ(X, C.U))
    (M := C.complex.toCochainComplex.homology j) (r j)).1
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ (r j)).1 h₄)

/-- A bounded complex of finite free modules vanishes above some degree. -/
theorem _root_.BoundedComplex.exists_rank_eq_zero_of_lt {A : Type*} [CommRing A]
    (M : BoundedComplex A) : ∃ b : ℤ, ∀ j, b < j → M.rank j = 0 := by
  obtain ⟨b, hb⟩ := M.bounded.bddAbove
  exact ⟨b, fun j hj => by
    by_contra h
    exact (not_le_of_gt hj) (hb h)⟩

include hrank in
/-- On a chart inside the open of constant ranks, at the index `k_i = r_{i+1} - r_{i+2} + ⋯` of
Stacks 0ESQ, the ideal of minors of `d^i` of size `ρ_i` is the unit ideal and that of size
`ρ_i + 1` vanishes, `ρ_i` being the rank of `d^i` there. -/
theorem AffineChart.fittingMinorIdeal_eq_top_and_eq_bot (C : AffineChart (ofPerfect X E hE))
    (hCU : (C.U : X.Opens) ≤ U) {m : ℤ} (hm : ∀ j, m < j → r j = 0) (i : ℤ) :
    C.complex.fittingMinorIdeal i (alternatingRankSum r m i) = ⊤ ∧
      C.complex.fittingMinorIdeal i (alternatingRankSum r m i - 1) = ⊥ := by
  obtain ⟨b, hb⟩ := C.complex.exists_rank_eq_zero_of_lt
  have hm' : ∀ j, max m b < j → C.complex.rank j = 0 := fun j hj => hb j (by omega)
  have hk : alternatingRankSum r (max m b) i = alternatingRankSum r m i :=
    alternatingRankSum_eq_of_vanishing hm (le_max_left m b) i
  have hH := fun j => C.isFiniteLocallyFreeOfRank_homology hE hrank hCU j
  obtain ⟨h1, h2⟩ := C.complex.minorIdeal_d_eq_top_and_minorIdeal_d_succ_eq_bot hm' r hH i
  rw [hk] at h1 h2
  refine ⟨h1, ?_⟩
  by_cases hnt : Nontrivial Γ(X, C.U)
  · obtain ⟨h0, -⟩ := C.complex.tailEulerCharacteristic_sub_alternatingRankSum_mem_Icc hm' r hH i
    rw [hk] at h0
    rw [BoundedComplex.fittingMinorIdeal,
      show C.complex.tailEulerCharacteristic (i + 1) - (alternatingRankSum r m i - 1) =
        (C.complex.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i) + 1 by ring]
    rwa [show (C.complex.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i + 1).toNat =
      (C.complex.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i).toNat + 1 by omega]
  · have : Subsingleton Γ(X, C.U) := not_nontrivial_iff_subsingleton.mp hnt
    exact Subsingleton.elim _ _

include hrank in
/-- If the cohomology of `E` is finite locally free of ranks `r` on a scheme-theoretically dense
open `U`, then the Fitting ideal sheaf `Fit_{i, k_i - 1}(E)` just below the index of Stacks 0ESQ
vanishes. -/
theorem chartFittingIdeal_alternatingRankSum_sub_one_eq_bot
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) {m : ℤ} (hm : ∀ j, m < j → r j = 0)
    (i : ℤ) :
    chartFittingIdeal (ofPerfect X E hE) (ofPerfect_cover hE) i
      (alternatingRankSum r m i - 1) = ⊥ := by
  have : IsSchemeTheoreticallyDominant U.ι :=
    Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense U hU
  refine Stacks.StrictTransformFittingRank.ideal_eq_bot_of_comap_eq_bot U.ι _ ?_
  let ι := {C : AffineChart (ofPerfect X E hE) // (C.U : X.Opens) ≤ U}
  let W : ι → U.toScheme.affineOpens := fun C =>
    ⟨U.ι ⁻¹ᵁ (C.1.U : X.Opens), C.1.U.2.preimage_of_isOpenImmersion U.ι
      (by rw [Scheme.Opens.opensRange_ι]; exact C.2)⟩
  refine le_bot_iff.mp (Scheme.IdealSheafData.le_of_iSup_eq_top W ?_ fun C => ?_)
  · refine top_le_iff.mp fun y _ => ?_
    obtain ⟨C, hy, hCU⟩ := exists_affineChart_ofPerfect hE (U.ι y) U y.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨C, hCU⟩, hy⟩
  · rw [Stacks.IdealSheaf.ideal_comap_appLE _ U.ι C.1.U (W C) le_rfl,
      ideal_chartFittingIdeal_self, (C.1.fittingMinorIdeal_eq_top_and_eq_bot hE hrank C.2 hm i).2,
      Ideal.map_bot]
    exact bot_le

include hrank in
/-- On every chart the ideal of minors just below the index of Stacks 0ESQ vanishes. -/
theorem AffineChart.fittingMinorIdeal_sub_one_eq_bot
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) {m : ℤ} (hm : ∀ j, m < j → r j = 0)
    (C : AffineChart (ofPerfect X E hE)) (i : ℤ) :
    C.complex.fittingMinorIdeal i (alternatingRankSum r m i - 1) = ⊥ := by
  rw [← ideal_chartFittingIdeal_self (ofPerfect_cover hE),
    chartFittingIdeal_alternatingRankSum_sub_one_eq_bot hE hrank hU hm i]
  rfl

include hrank in
/-- The minor size of Stacks 0ESQ is nonnegative on every nonempty chart: the index
`k_i = r_{i+1} - r_{i+2} + ⋯` does not exceed `n_{i+1} - n_{i+2} + ⋯` for the ranks `n_j` of the
chart complex. -/
theorem AffineChart.alternatingRankSum_le_tailEulerCharacteristic
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) {m : ℤ} (hm : ∀ j, m < j → r j = 0)
    (C : AffineChart (ofPerfect X E hE)) [Nontrivial Γ(X, C.U)] (i : ℤ) :
    alternatingRankSum r m i ≤ C.complex.tailEulerCharacteristic (i + 1) := by
  by_contra h
  have h0 := C.fittingMinorIdeal_sub_one_eq_bot hE hrank hU hm i
  rw [BoundedComplex.fittingMinorIdeal, Int.toNat_of_nonpos (by omega), minorIdeal_zero] at h0
  exact top_ne_bot h0

/-- A nonempty affine open has a nontrivial ring of sections. -/
private theorem nontrivial_sections_of_mem {V : X.Opens} (hV : IsAffineOpen V) {x : X}
    (hx : x ∈ V) : Nontrivial Γ(X, V) := by
  by_contra h
  have : Subsingleton Γ(X, V) := not_nontrivial_iff_subsingleton.mp h
  have hx' : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hx
  obtain ⟨q, -⟩ := hx'
  exact (PrimeSpectrum.isEmpty_iff_subsingleton.mpr this).false q

include hrank in
/-- On every chart only finitely many of the Fitting minor ideals at the indices `k_i` are
proper. -/
theorem AffineChart.exists_finset_fittingMinorIdeal_eq_top
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) {m : ℤ} (hm : ∀ j, m < j → r j = 0)
    (C : AffineChart (ofPerfect X E hE)) :
    ∃ T : Finset ℤ, ∀ i ∉ T, C.complex.fittingMinorIdeal i (alternatingRankSum r m i) = ⊤ := by
  classical
  by_cases hnt : Nontrivial Γ(X, C.U)
  swap
  · have : Subsingleton Γ(X, C.U) := not_nontrivial_iff_subsingleton.mp hnt
    exact ⟨∅, fun i _ => Subsingleton.elim _ _⟩
  obtain ⟨b, hb⟩ := C.complex.exists_rank_eq_zero_of_lt
  obtain ⟨a, ha⟩ := C.complex.bounded.bddBelow
  have ha' : ∀ j, j < a → C.complex.rank j = 0 := fun j hj => by
    by_contra h
    exact (not_le_of_gt hj) (ha h)
  refine ⟨Finset.Icc (a - 1) (max b m), fun i hi => ?_⟩
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
  rcases hi with hi | hi
  · obtain ⟨p⟩ : Nonempty (PrimeSpectrum Γ(X, C.U)) := inferInstance
    have hxC : C.U.2.fromSpec p ∈ (C.U : X.Opens) := by
      rw [← SetLike.mem_coe, ← C.U.2.range_fromSpec]
      exact ⟨p, rfl⟩
    obtain ⟨y, hyC, hyU⟩ := (dense_of_isSchemeTheoreticallyDense U hU).inter_open_nonempty
      (C.U : Set X) (C.U : X.Opens).isOpen ⟨_, hxC⟩
    obtain ⟨D, hyD, hDle⟩ := exists_affineChart_ofPerfect hE y (C.U ⊓ U) ⟨hyC, hyU⟩
    have hntD := nontrivial_sections_of_mem D.U.2 hyD
    have hmap := AffineChart.map_fittingMinorIdeal_eq C D (hDle.trans inf_le_left) i
      (alternatingRankSum r m i)
    rw [(D.fittingMinorIdeal_eq_top_and_eq_bot hE hrank (hDle.trans inf_le_right) hm i).1] at hmap
    rw [BoundedComplex.fittingMinorIdeal]
    by_cases hs : (C.complex.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i).toNat = 0
    · rw [hs, minorIdeal_zero]
    · have hbot : minorIdeal (C.complex.d i)
          (C.complex.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i).toNat = ⊥ :=
        minorIdeal_eq_bot_of_card_lt _ _ (Or.inl (by
          rw [Fintype.card_fin, ha' (i + 1) (by omega)]
          omega))
      rw [BoundedComplex.fittingMinorIdeal, hbot, Ideal.map_bot] at hmap
      exact (bot_ne_top hmap).elim
  · rw [BoundedComplex.fittingMinorIdeal,
      C.complex.tailEulerCharacteristic_eq_zero_of_lt hb (by omega),
      alternatingRankSum_of_le (by omega), sub_zero, Int.toNat_zero, minorIdeal_zero]

variable (r) in
/-- The Fitting ideal sheaf `Fit_{i, k_i}(E)` of Stacks 0ESQ, at the index
`k_i = r_{i+1} - r_{i+2} + ⋯ + (-1)^{m-i+1} r_m`. -/
abbrev fittingIdealOfRanks (m i : ℤ) : X.IdealSheafData :=
  chartFittingIdeal (ofPerfect X E hE) (ofPerfect_cover hE) i (alternatingRankSum r m i)

include hrank in
/-- The supports of the Fitting ideal sheaves `Fit_{i, k_i}(E)` form a locally finite family:
locally on `X` almost all of these ideals are the unit ideal. -/
theorem locallyFinite_support_fittingIdealOfRanks
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) {m : ℤ} (hm : ∀ j, m < j → r j = 0) :
    LocallyFinite fun i => ((fittingIdealOfRanks hE r m i).support : Set X) := by
  intro x
  obtain ⟨C, hx⟩ := ofPerfect_cover hE x
  obtain ⟨T, hT⟩ := C.exists_finset_fittingMinorIdeal_eq_top hE hrank hU hm
  refine ⟨C.U, (C.U : X.Opens).isOpen.mem_nhds hx, T.finite_toSet.subset fun i hi => ?_⟩
  by_contra hiT
  obtain ⟨y, hyI, hyC⟩ := hi
  have hdisj := Scheme.IdealSheafData.disjoint_support_of_forall_exists_ideal_eq_top
    (fittingIdealOfRanks hE r m i) C.U fun z hz =>
      ⟨C.U, hz, (ideal_chartFittingIdeal_self (ofPerfect_cover hE) i _ C).trans (hT i hiT)⟩
  exact Set.disjoint_left.mp hdisj hyC hyI

include hrank in
/-- The supports of the Fitting ideal sheaves avoid the open of constant ranks. -/
theorem disjoint_support_fittingIdealOfRanks {m : ℤ} (hm : ∀ j, m < j → r j = 0) (i : ℤ) :
    Disjoint (U : Set X) ((fittingIdealOfRanks hE r m i).support : Set X) :=
  Scheme.IdealSheafData.disjoint_support_of_forall_exists_ideal_eq_top _ U fun x hx => by
    obtain ⟨C, hxC, hCU⟩ := exists_affineChart_ofPerfect hE x U hx
    exact ⟨C.U, hxC, (ideal_chartFittingIdeal_self (ofPerfect_cover hE) i _ C).trans
      (C.fittingMinorIdeal_eq_top_and_eq_bot hE hrank hCU hm i).1⟩

/-- The Fitting ideal sheaves `Fit_{i, k_i}(E)` are of finite type. -/
theorem isFiniteType_fittingIdealOfRanks (m i : ℤ) :
    (fittingIdealOfRanks hE r m i).IsFiniteType :=
  Scheme.IdealSheafData.isFiniteType_ofAffineFamily _ _ _ _ _ fun V ⟨C, hC⟩ => by
    rw [chartFittingFamily_eq _ _ C V hC]
    exact (C.complex.fittingMinorIdeal_fg _ _).map _

variable (r) in
/-- The centre of the blowup of Stacks 0ESQ: the product of the locally finite family of
Fitting ideal sheaves `Fit_{i, k_i}(E)`, `i ∈ ℤ`. -/
abbrev fittingIdealProdOfRanks (m : ℤ)
    (hlf : LocallyFinite fun i => ((fittingIdealOfRanks hE r m i).support : Set X)) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.locallyFiniteProd (fittingIdealOfRanks hE r m) hlf

include hrank in
/-- The blowup in the product of the Fitting ideal sheaves is `U`-admissible: the centre is of
finite type and its support, the union of the supports of the factors, avoids `U`. -/
@[stacks 0ESQ "the U-admissible blowup, in the product of the Fitting ideals of the complex"]
theorem isAdmissibleBlowup_fittingIdealProdOfRanks {m : ℤ} (hm : ∀ j, m < j → r j = 0)
    (hlf : LocallyFinite fun i => ((fittingIdealOfRanks hE r m i).support : Set X)) :
    Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase (fittingIdealProdOfRanks hE r m hlf)) := by
  refine (Stacks.Blowup.isAdmissibleBlowup_iff U _).mpr
    ⟨fittingIdealProdOfRanks hE r m hlf, ?_, ?_, Iso.refl _, Category.id_comp _⟩
  · rw [finitePresentation_subschemeι_iff_isFiniteType]
    exact Scheme.IdealSheafData.fg_ideal_locallyFiniteProd _ hlf
      (fun i => isFiniteType_fittingIdealOfRanks hE m i)
  · rw [Scheme.IdealSheafData.coe_support_locallyFiniteProd, Set.disjoint_iUnion_right]
    exact fun i => disjoint_support_fittingIdealOfRanks hE hrank hm i

/-- On the blowup in the product of the Fitting ideal sheaves, the inverse image of each
`Fit_{i, k_i}(E)` is an effective Cartier divisor. -/
@[stacks 0ESQ "the Fitting ideals of the complex become effective Cartier divisors"]
theorem isEffectiveCartierDivisor_comap_fittingIdealOfRanks {m : ℤ}
    (hlf : LocallyFinite fun i => ((fittingIdealOfRanks hE r m i).support : Set X)) (i : ℤ) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((fittingIdealOfRanks hE r m i).comap
        (blowUpToBase (fittingIdealProdOfRanks hE r m hlf))) := by
  classical
  set b := blowUpToBase (fittingIdealProdOfRanks hE r m hlf)
  have h : Stacks.Divisors.IsEffectiveCartierDivisor
      ((fittingIdealProdOfRanks hE r m hlf).comap b) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  have e : fittingIdealProdOfRanks hE r m hlf = _ :=
    Scheme.IdealSheafData.locallyFiniteProd_eq_mul _ hlf i
  rw [congrArg (fun I : X.IdealSheafData => I.comap b) e, comap_mul] at h
  exact isEffectiveCartierDivisor_left_of_mul _ _ h

/-- The empty divisor pulls back along any morphism. -/
theorem isPullbackDefined_ofPerfect {Y : Scheme.{u}} (f : Y ⟶ X) :
    Stacks.Divisors.IsPullbackDefined f (ofPerfect X E hE).D := by
  show Stacks.Divisors.IsEffectiveCartierDivisor ((⊤ : X.IdealSheafData).comap f)
  rw [Scheme.IdealSheafData.comap_top]
  exact Stacks.Divisors.isEffectiveCartierDivisor_top

include hrank in
/-- On the blowup, every point lies in an affine chart of the pulled-back complex whose Fitting
minor ideals at the indices `k_i` are generated by nonzerodivisors, whose next Fitting minor ideals
vanish, and on which the minor sizes are nonnegative. -/
theorem exists_affineChart_pullback_fittingMinorIdeal
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) {m : ℤ} (hm : ∀ j, m < j → r j = 0)
    (hlf : LocallyFinite fun i => ((fittingIdealOfRanks hE r m i).support : Set X))
    (y : blowUp (fittingIdealProdOfRanks hE r m hlf)) :
    ∃ C : AffineChart ((ofPerfect X E hE).pullback
        (blowUpToBase (fittingIdealProdOfRanks hE r m hlf)) (isPullbackDefined_ofPerfect hE _)),
      y ∈ C.U.1 ∧
      (∀ i, ∃ g, IsRegular g ∧
        C.complex.fittingMinorIdeal i (alternatingRankSum r m i) = Ideal.span {g}) ∧
      (∀ i, C.complex.fittingMinorIdeal i (alternatingRankSum r m i - 1) = ⊥) ∧
      ∀ i, alternatingRankSum r m i ≤ C.complex.tailEulerCharacteristic (i + 1) := by
  classical
  set b := blowUpToBase (fittingIdealProdOfRanks hE r m hlf)
  obtain ⟨C, hx⟩ := ofPerfect_cover hE (b y)
  obtain ⟨T, hT⟩ := C.exists_finset_fittingMinorIdeal_eq_top hE hrank hU hm
  have hcart := fun i => isEffectiveCartierDivisor_comap_fittingIdealOfRanks hE hlf i
  choose W hW hyW g hg hgen using fun i =>
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor _ (hcart i) y
  let N := b ⁻¹ᵁ (C.U : X.Opens) ⊓ ⨅ i : T, W i
  have hyN : y ∈ N := ⟨hx, by
    simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact fun i => hyW i⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVN⟩ :=
    (blowUp (fittingIdealProdOfRanks hE r m hlf)).isBasis_affineOpens.exists_subset_of_mem_open
      hyN N.isOpen
  have hVC : V ≤ b ⁻¹ᵁ (C.U : X.Opens) := hVN.trans inf_le_left
  have hVW : ∀ i ∈ T, V ≤ W i := fun i hi =>
    hVN.trans (inf_le_right.trans (iInf_le (fun i : T => W i) ⟨i, hi⟩))
  let C'' := C.pullback b (isPullbackDefined_ofPerfect hE b) ⟨V, hV⟩ hVC
  have hnt := nontrivial_sections_of_mem C.U.2 hx
  have hfit : ∀ i k : ℤ, C''.complex.fittingMinorIdeal i k =
      Ideal.map (b.appLE (C.U : X.Opens) V hVC).hom (C.complex.fittingMinorIdeal i k) :=
    fun i k => (BoundedComplex.map_fittingMinorIdeal _ C.complex i k).symm
  refine ⟨C'', hyV, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · by_cases hi : i ∈ T
    · refine ⟨(blowUp (fittingIdealProdOfRanks hE r m hlf)).presheaf.map
        (homOfLE (hVW i hi)).op (g i),
        IsAffineOpen.isRegular_presheaf_map_of_le (hW i) hV (hVW i hi) (hg i), ?_⟩
      rw [hfit, ← ideal_chartFittingIdeal_self (ofPerfect_cover hE) i _ C,
        ← Stacks.IdealSheaf.ideal_comap_appLE _ b C.U ⟨V, hV⟩ hVC,
        ← Scheme.IdealSheafData.map_ideal (U := ⟨V, hV⟩) (V := ⟨W i, hW i⟩) _ (hVW i hi),
        hgen i, Ideal.map_span, Set.image_singleton]
      rfl
    · refine ⟨1, isRegular_one, ?_⟩
      rw [hfit, hT i hi, Ideal.map_top, Ideal.span_singleton_one]
      rfl
  · rw [hfit, C.fittingMinorIdeal_sub_one_eq_bot hE hrank hU hm i, Ideal.map_bot]
    rfl
  · exact C.alternatingRankSum_le_tailEulerCharacteristic hE hrank hU hm i

include hrank in
/-- On the blowup of `X` in the product of the Fitting ideal sheaves, every cohomology sheaf of
the pulled-back perfect object is perfect of Tor dimension at most one. -/
theorem isPerfect_and_hasTorAmplitude_homology_pullback
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) {m : ℤ} (hm : ∀ j, m < j → r j = 0)
    (hlf : LocallyFinite fun i => ((fittingIdealOfRanks hE r m i).support : Set X)) (i : ℤ) :
    IsPerfect.{u, u, u + 1}
        (X := (blowUp (fittingIdealProdOfRanks hE r m hlf)).toRingedSpace)
        ((DerivedCategory.singleFunctor (blowUp (fittingIdealProdOfRanks hE r m hlf)).Modules 0).obj
          ((DerivedCategory.homologyFunctor
            (OXMod (blowUp (fittingIdealProdOfRanks hE r m hlf)).toRingedSpace) i).obj
            ((ofPerfect X E hE).derivedPullbackObject
              (blowUpToBase (fittingIdealProdOfRanks hE r m hlf))))) ∧
      HasTorAmplitude (blowUp (fittingIdealProdOfRanks hE r m hlf)).toRingedSpace
        ((DerivedCategory.singleFunctor (blowUp (fittingIdealProdOfRanks hE r m hlf)).Modules 0).obj
          ((DerivedCategory.homologyFunctor
            (OXMod (blowUp (fittingIdealProdOfRanks hE r m hlf)).toRingedSpace) i).obj
            ((ofPerfect X E hE).derivedPullbackObject
              (blowUpToBase (fittingIdealProdOfRanks hE r m hlf))))) (-1) 0 := by
  refine isPerfect_and_hasTorAmplitude_of_forall_restrict _ (-1) 0 fun y => ?_
  obtain ⟨C, hyC, hprin, hpred, hle⟩ :=
    exists_affineChart_pullback_fittingMinorIdeal hE hrank hU hm hlf y
  choose g hg hgen using hprin
  let ρ : ℤ → ℕ := fun j =>
    (C.complex.tailEulerCharacteristic (j + 1) - alternatingRankSum r m j).toNat
  have hρ : ∀ j, minorIdeal (C.complex.d j) (ρ j) = Ideal.span {g j} := hgen
  have hρ' : ∀ j, minorIdeal (C.complex.d j) (ρ j + 1) = ⊥ := fun j => by
    have h := hpred j
    have h0 := hle j
    rwa [BoundedComplex.fittingMinorIdeal,
      show (C.complex.tailEulerCharacteristic (j + 1) - (alternatingRankSum r m j - 1)).toNat =
        ρ j + 1 by simp only [ρ]; omega] at h
  obtain ⟨T, hT, h₁, h₂, h₃, h₄, ⟨e⟩⟩ :=
    C.complex.exists_shortExact_homology_of_minorIdeal ρ g hg hρ hρ' i
  exact ⟨C.U.1, hyC, AffineChart.isPerfect_and_hasTorAmplitude_restrict_homology C i T hT e⟩

/-- The derived pullback of the perfect object of the situation `(X, ∅, E)` is the derived
pullback of `E`. -/
def derivedPullbackObjectOfPerfectIso {Y : Scheme.{u}} (f : Y ⟶ X) :
    (ofPerfect X E hE).derivedPullbackObject f ≅ (derivedPullback f.toLRSHom.toShHom).obj E :=
  (derivedPullback f.toLRSHom.toShHom).mapIso
    ((Localization.uniq (DerivedCategory.Q (C := OXMod.{u, u} X.toRingedSpace))
        (DerivedCategory.Q (C := OXMod.{u, u} X.toRingedSpace))
        (HomologicalComplex.quasiIso (OXMod.{u, u} X.toRingedSpace)
          (ComplexShape.up ℤ))).functor.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
      (Localization.compUniqFunctor (DerivedCategory.Q (C := OXMod.{u, u} X.toRingedSpace))
        (DerivedCategory.Q (C := OXMod.{u, u} X.toRingedSpace))
        (HomologicalComplex.quasiIso (OXMod.{u, u} X.toRingedSpace)
          (ComplexShape.up ℤ))).app _ ≪≫ DerivedCategory.Q.objObjPreimageIso E)

include hrank in
/-- The ranks `r_j` vanish above the top degree of a nonempty chart inside the open of constant
ranks. -/
theorem AffineChart.rank_eq_zero_of_lt (C : AffineChart (ofPerfect X E hE))
    (hCU : (C.U : X.Opens) ≤ U) [Nontrivial Γ(X, C.U)] {b : ℤ}
    (hb : ∀ j, b < j → C.complex.rank j = 0) (j : ℤ) (hj : b < j) : r j = 0 := by
  have hX : IsZero (C.complex.toCochainComplex.X j) := by
    show IsZero (ModuleCat.of Γ(X, C.U) (Fin (C.complex.rank j) → Γ(X, C.U)))
    rw [hb j hj]
    exact ModuleCat.isZero_of_subsingleton _
  have : Subsingleton (C.complex.toCochainComplex.homology j) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (ShortComplex.isZero_homology_of_isZero_X₂ (C.complex.toCochainComplex.sc j) hX)
  exact (C.isFiniteLocallyFreeOfRank_homology hE hrank hCU j).eq_zero_of_subsingleton

end Rank

end AlgebraicGeometry.ComplexAndDivisorSituation

namespace AlgebraicGeometry

open ComplexAndDivisorSituation

/-- For a morphism `b : Y ⟶ X` and a degree `i`, the `i`-th cohomology module of the derived
pullback of `E` along `b` is a perfect `𝒪_Y`-module of Tor dimension at most one. -/
def IsHomologyPerfectTorLEOne {X : Scheme.{u}} (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    {Y : Scheme.{u}} (b : Y ⟶ X) (i : ℤ) : Prop :=
  IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y.toRingedSpace) i).obj
          ((derivedPullback b.toLRSHom.toShHom).obj E))) ∧
    HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y.toRingedSpace) i).obj
          ((derivedPullback b.toLRSHom.toShHom).obj E))) (-1) 0

/-- A nonempty affine open has a nontrivial ring of sections. -/
theorem IsAffineOpen.nontrivial_of_mem {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    {x : X} (hx : x ∈ V) : Nontrivial Γ(X, V) :=
  nontrivial_sections_of_mem hV hx

/-- Let `X` be a scheme, let `E ∈ D(𝒪_X)` be perfect, and let `U ⊆ X` be a scheme-theoretically
dense open subscheme such that `H^i(E|_U)` is finite locally free of constant rank `r_i` for every
`i`. Then there is a `U`-admissible blowup `b : X' ⟶ X` such that `H^i(Lb^*E)` is a perfect
`𝒪_{X'}`-module of Tor dimension at most one for every `i`. -/
@[stacks 0ESQ]
theorem exists_admissibleBlowup_forall_isHomologyPerfectTorLEOne {X : Scheme.{u}}
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (U : X.Opens)
    (dense : Scheme.Opens.IsSchemeTheoreticallyDense U) (perfect : IsPerfect.{u, u, u + 1} E)
    (r : ℤ → ℕ)
    (homology_rank : ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} U.toScheme.toRingedSpace) i).obj
        ((derivedPullback U.ι.toLRSHom.toShHom).obj E)) (r i)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      Stacks.Blowup.IsAdmissibleBlowup U b ∧ ∀ i : ℤ, IsHomologyPerfectTorLEOne E b i := by
  by_cases hUne : (U : Set X).Nonempty
  · obtain ⟨x, hx⟩ := hUne
    obtain ⟨C₀, hxC, hCU⟩ := exists_affineChart_ofPerfect perfect x U hx
    have := C₀.U.2.nontrivial_of_mem hxC
    obtain ⟨m, hmC⟩ := C₀.complex.exists_rank_eq_zero_of_lt
    have hm : ∀ j, m < j → r j = 0 := C₀.rank_eq_zero_of_lt perfect homology_rank hCU hmC
    have hlf := locallyFinite_support_fittingIdealOfRanks perfect homology_rank dense hm
    refine ⟨_, blowUpToBase (fittingIdealProdOfRanks perfect r m hlf),
      isAdmissibleBlowup_fittingIdealProdOfRanks perfect homology_rank hm hlf, fun i => ?_⟩
    obtain ⟨h₁, h₂⟩ :=
      isPerfect_and_hasTorAmplitude_homology_pullback perfect homology_rank dense hm hlf i
    let e := (DerivedCategory.singleFunctor
      (blowUp (fittingIdealProdOfRanks perfect r m hlf)).Modules 0).mapIso
        ((DerivedCategory.homologyFunctor
        (OXMod (blowUp (fittingIdealProdOfRanks perfect r m hlf)).toRingedSpace) i).mapIso
        (derivedPullbackObjectOfPerfectIso perfect
          (blowUpToBase (fittingIdealProdOfRanks perfect r m hlf))))
    exact ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
      (X := (blowUp (fittingIdealProdOfRanks perfect r m hlf)).toRingedSpace) e h₁,
      Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} h₂ e.symm⟩
  · have hXe : IsEmpty X := ⟨fun x => by
      have h := dense_of_isSchemeTheoreticallyDense U dense
      rw [Set.not_nonempty_iff_eq_empty.mp hUne, dense_iff_closure_eq, closure_empty] at h
      exact (h.symm ▸ Set.mem_univ x : x ∈ (∅ : Set X))⟩
    refine ⟨_, blowUpToBase (⊤ : X.IdealSheafData), ?_, fun i => ?_⟩
    · refine (Stacks.Blowup.isAdmissibleBlowup_iff U _).mpr ⟨⊤, ?_, ?_, Iso.refl _,
        Category.id_comp _⟩
      · rw [finitePresentation_subschemeι_iff_isFiniteType]
        exact fun V => ⟨{1}, by simp [Scheme.IdealSheafData.ideal_top]⟩
      · rw [Scheme.IdealSheafData.support_top]
        exact disjoint_bot_right
    · have : IsEmpty (blowUp (⊤ : X.IdealSheafData)) :=
        ⟨fun y => hXe.false (blowUpToBase (⊤ : X.IdealSheafData) y)⟩
      exact isPerfect_and_hasTorAmplitude_of_forall_restrict _ (-1) 0
        fun y => (IsEmpty.false y).elim

end AlgebraicGeometry
