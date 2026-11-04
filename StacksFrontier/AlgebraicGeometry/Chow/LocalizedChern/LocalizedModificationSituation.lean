module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedComposite

/-!
# Condition (2) of Situation 0GUJ on a modification of the projective line

Let `(S, δ)`, `X`, `i : Z ⟶ X`, `F ∈ D(𝒪_X)` and `p` be as in Situation 0GUJ, let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre at infinity
`i_∞ : W_∞ ⟶ W` and projection `π : W ⟶ X`, and let `Q ∈ D(𝒪_W)` be perfect. Assume that the
restriction of `Q` to `b^{-1}(𝐀¹_X)` is the pullback of `F`, and that there is a closed
`T ⊆ W_∞` containing every point of `W_∞` lying over `X ∖ Z` on which `Q` is zero, resp. a
finite locally free module of rank `< p` placed in degree `0`. These are the hypotheses of
Stacks 0FE8. Its proof uses the situation of Stacks 0GUJ for `W`, the closed subscheme
`W_Z = π^{-1}(Z)` and `Q` (`Stacks.Chow.modificationSituationOf`). This file proves its condition
(2): `Q` is zero, resp. finite locally free of rank `< p` in degree `0`, on `W ∖ W_Z`. A point of
`W ∖ W_Z` lies either on `b^{-1}(𝐀¹_X)`, over `X ∖ Z`, where `Q` is the pullback of `F`, or on
`W_∞`, where it lies on `T`.

Condition (2) is checked pointwise. A perfect object is zero, resp. finite locally free of rank
`< p` in degree `0`, on an open containing every point at which its cohomology stalks are finite
free of fibre rank `0` in nonzero degrees and of fibre rank `< p` in degree `0` (Stacks 0GT1, as
`Stacks.Chow.exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT`); and these pointwise
conditions hold at every point at which the derived fibre vanishes, resp. at every point of a
scheme mapping to `X` along which the object pulls back to such a module (Stacks 0BCD).

## Main results

* `Stacks.Chow.LocalizedSituation.modificationRestriction_of_isZero`,
  `Stacks.Chow.LocalizedSituation.modificationRestriction_of_rankLT` — condition (2) for
  `W`, `W_Z`, `Q`.
* `Stacks.Chow.LocalizedSituation.isZero_pullback_restriction`,
  `Stacks.Chow.LocalizedSituation.exists_rankLT_pullback_restriction` — condition (2) for
  `W`, `W_Z`, `π^* F`.
* `Stacks.Chow.mem_cohomologyFiniteFreeLocus_of_isZero_fibre`,
  `Stacks.Chow.mem_cohomologyFiniteFreeLocus_of_rankLT` — the pointwise conditions.
* `Stacks.Chow.exists_iso_singleFunctor_of_forall_mem`, `Stacks.Chow.isZero_of_forall_mem` — a
  perfect object is finite locally free of rank `< p` in degree `0`, resp. zero, on an open all
  of whose points satisfy the pointwise conditions.

## References

* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 0GT1](https://stacks.math.columbia.edu/tag/0GT1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The pointwise conditions -/

section Pointwise

variable {X : Scheme.{u}} (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)

include hE in
/-- **A point at which the derived fibre of a perfect object vanishes** lies in the finite free
locus of Stacks 0GT1, with all cohomology sheaves of fibre rank `0` there: by derived Nakayama
the derived stalk vanishes. -/
theorem mem_cohomologyFiniteFreeLocus_of_isZero_fibre (x : X)
    (h : IsZero ((derivedPullback (X.fromSpecResidueField x).toLRSHom.toShHom).obj E)) :
    x ∈ RingedSpace.cohomologyFiniteFreeLocus E ∧
      (∀ n : ℤ, n ≠ 0 → Scheme.Modules.fiberRank
        ((DerivedCategory.homologyFunctor X.Modules n).obj E) x = 0) ∧
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules 0).obj E) x < 1 := by
  obtain ⟨hx₁, hx₂⟩ := mem_cohomologyFiniteFreeLocus_of_isZero_derivedStalkFunctor E x
    (isZero_derivedStalkFunctor_obj_of_isZero_derivedPullback E hE x h)
  exact ⟨hx₁, fun n _ => hx₂ n, (hx₂ 0).trans_lt Nat.one_pos⟩

include hE in
/-- **A point of the image of a scheme along which a perfect object pulls back to a finite
locally free module of rank `< p` in degree `0`** lies in the finite free locus of Stacks 0GT1,
with the cohomology sheaves in nonzero degrees of fibre rank `0` and `H^0` of fibre rank `< p`
there: the derived fibre is computed on the source, and its Euler characteristic is the fibre rank
of `H^0`. -/
theorem mem_cohomologyFiniteFreeLocus_of_rankLT {X₁ : Scheme.{u}} (i₁ : X₁ ⟶ X) {p : ℕ}
    (hrank : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((derivedPullback i₁.toLRSHom.toShHom).obj E ≅
        (DerivedCategory.singleFunctor _ 0).obj M)) (y : X₁) :
    i₁ y ∈ RingedSpace.cohomologyFiniteFreeLocus E ∧
      (∀ n : ℤ, n ≠ 0 → Scheme.Modules.fiberRank
        ((DerivedCategory.homologyFunctor X.Modules n).obj E) (i₁ y) = 0) ∧
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules 0).obj E) (i₁ y) <
        p := by
  obtain ⟨M₁, hM₁, ⟨e₁⟩⟩ := hrank
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M₁ := hM₁.1
  obtain ⟨hx, h0⟩ := mem_cohomologyFiniteFreeLocus_of_iso_singleFunctor E hE i₁ M₁ e₁ y
  refine ⟨hx, h0, ?_⟩
  have hpc₁ := DerivedFibreBetti.isPseudoCoherent_derivedPullback i₁ E
    (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE)
  have hpc' : RingedSpace.IsPseudoCoherent (X := X₁.toRingedSpace)
      ((DerivedCategory.singleFunctor _ 0).obj M₁) := by
    obtain ⟨K, hK, ⟨v⟩⟩ := hpc₁
    exact ⟨K, hK, ⟨v ≪≫ e₁⟩⟩
  obtain ⟨V, hyV, r, hrp, hr⟩ := hM₁.2 y
  have h1 := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback i₁ E
    (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE)) y
  have h2 := congrFun (DerivedFibreBetti.chiDerivedFibre_congr _ hpc₁ hpc' e₁) y
  have h3 := DerivedFibreBetti.chiDerivedFibre_singleFunctor_eq_of_restrict X₁ M₁ hpc' V r hr y
    hyV
  have h4 : DerivedFibreBetti.chiDerivedFibre X E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E hE) (i₁ y) = r :=
    h1.symm.trans (h2.trans h3)
  have h5 := chiDerivedFibre_eq_fiberRank E hE _ hx h0
  omega

include hE in
/-- **A perfect object is a finite locally free module of rank `< p` in degree `0` on an open all
of whose points satisfy the pointwise conditions.** -/
theorem exists_iso_singleFunctor_of_forall_mem (U : X.Opens) (p : ℕ)
    (hU : ∀ x ∈ U, x ∈ RingedSpace.cohomologyFiniteFreeLocus E ∧
      (∀ n : ℤ, n ≠ 0 → Scheme.Modules.fiberRank
        ((DerivedCategory.homologyFunctor X.Modules n).obj E) x = 0) ∧
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules 0).obj E) x < p) :
    ∃ M : OXMod.{u, u, u} (X.toRingedSpace.restrict U.isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p ∧
        Nonempty ((derivedPullback (X.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj E ≅
          (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨U', hU', hrest⟩ := exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT E hE p
  have hle : U ≤ U' := fun x hx => hU' x (hU x hx).1 (hU x hx).2.1 (hU x hx).2.2
  exact exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors (i := U'.ι) (k := U.ι)
    (X.homOfLE_ι hle) hrest

include hE in
/-- **A perfect object vanishes on an open all of whose points satisfy the pointwise conditions
for the bound `1`.** -/
theorem isZero_of_forall_mem (U : X.Opens)
    (hU : ∀ x ∈ U, x ∈ RingedSpace.cohomologyFiniteFreeLocus E ∧
      (∀ n : ℤ, n ≠ 0 → Scheme.Modules.fiberRank
        ((DerivedCategory.homologyFunctor X.Modules n).obj E) x = 0) ∧
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor X.Modules 0).obj E) x < 1) :
    IsZero ((derivedPullback (X.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj E) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_iso_singleFunctor_of_forall_mem E hE U 1 hU
  have hM0 : IsZero M := isZero_of_isFiniteLocallyFreeOfRankLT_one (W := U.toScheme) (M := M) hM
  exact (Functor.map_isZero (DerivedCategory.singleFunctor _ 0) hM0).of_iso e

end Pointwise

/-! ### Condition (2) on the modification -/

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) {W T : Scheme.{u}}
  (b : W ⟶ projectiveLineProduct S.a)
  (t : T ⟶ modificationFibreAtInfinity S.a b) [IsClosedImmersion t]
  {Q : DerivedCategory W.Modules}

/-- The open subscheme `X ∖ Z` of `X`. -/
abbrev complementOpens : S.X.Opens :=
  ⟨(Set.range S.i.base)ᶜ, S.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The open subscheme of the chart `b^{-1}(𝐀¹_X)` lying over `X ∖ Z`. -/
abbrev modificationChartComplement : (Limits.pullback b (projectiveLineAffineChart S.a)).Opens :=
  (pullback.fst b (projectiveLineAffineChart S.a) ≫ modificationProjection S.a b) ⁻¹ᵁ
    S.complementOpens

/-- Every point of `W` lies on the chart `b^{-1}(𝐀¹_X)` or on the fibre at infinity. -/
theorem mem_range_affineChart_or_mem_range_infinity (w : W) :
    w ∈ Set.range (pullback.fst b (projectiveLineAffineChart S.a)) ∨
      w ∈ Set.range (modificationInclusionAtInfinity S.a b) := by
  rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
  by_cases h : b w ∈ Set.range (projectiveLineAffineChart S.a)
  · exact Or.inl h
  · refine Or.inr ?_
    rw [← compl_range_projectiveLineAffineChart]
    exact h

/-- A point of the chart lying over `X ∖ Z` lies in the open subscheme over `X ∖ Z`. -/
theorem mem_modificationChartComplement
    {u : ↥(Limits.pullback b (projectiveLineAffineChart S.a))}
    (hu : modificationProjection S.a b (pullback.fst b (projectiveLineAffineChart S.a) u) ∉
      Set.range S.i) :
    u ∈ S.modificationChartComplement b := by
  intro hz
  exact hu (by simpa only [Scheme.Hom.comp_apply] using hz)

/-- The part of the chart lying over `X ∖ Z` maps to `X ∖ Z`. -/
theorem range_modificationChartComplement_subset :
    Set.range ((S.modificationChartComplement b).ι ≫
        pullback.fst b (projectiveLineAffineChart S.a) ≫ modificationProjection S.a b) ⊆
      Set.range (S.complementOpens).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  exact x.2

/-- The part of the chart lying over `X ∖ Z` factors through `X ∖ Z`. -/
theorem modificationChartComplement_fac :
    IsOpenImmersion.lift (S.complementOpens).ι
        ((S.modificationChartComplement b).ι ≫ pullback.fst b (projectiveLineAffineChart S.a) ≫
          modificationProjection S.a b) (S.range_modificationChartComplement_subset b) ≫
        (S.complementOpens).ι =
      ((S.modificationChartComplement b).ι ≫ pullback.fst b (projectiveLineAffineChart S.a)) ≫
        modificationProjection S.a b := by
  rw [IsOpenImmersion.lift_fac, Category.assoc]

omit [IsClosedImmersion t] in
include t in
/-- A point of the fibre at infinity lying over `X ∖ Z` lies on `T`. -/
theorem mem_range_of_mem_range_infinity
    (hT : ∀ w, modificationProjectionAtInfinity S.a b w ∉ Set.range S.i → w ∈ Set.range t)
    {w : W} (hw : modificationProjection S.a b w ∉ Set.range S.i)
    (hinf : w ∈ Set.range (modificationInclusionAtInfinity S.a b)) :
    w ∈ Set.range (t ≫ modificationInclusionAtInfinity S.a b) := by
  obtain ⟨w', rfl⟩ := hinf
  obtain ⟨τ, hτ⟩ := hT w' fun hz => hw (by
    simpa only [modificationProjectionAtInfinity, Scheme.Hom.comp_apply] using hz)
  exact ⟨τ, by rw [Scheme.Hom.comp_apply, hτ]⟩

variable {b}

/-- Restricting the isomorphism `hF` to the part of the chart lying over `X ∖ Z`. -/
private theorem nonempty_iso_modificationChartComplement
    (hF : Nonempty ((derivedPullback
        (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q ≅
      (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a) ≫
        modificationProjection S.a b).toLRSHom.toShHom).obj S.E)) :
    Nonempty ((derivedPullback ((S.modificationChartComplement b).ι ≫
        pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q ≅
      (derivedPullback (((S.modificationChartComplement b).ι ≫
        pullback.fst b (projectiveLineAffineChart S.a)) ≫
          modificationProjection S.a b).toLRSHom.toShHom).obj S.E) :=
  ⟨(derivedPullbackCompIsoOfScheme (S.modificationChartComplement b).ι
    (pullback.fst b (projectiveLineAffineChart S.a)) Q).symm ≪≫
    (derivedPullback (S.modificationChartComplement b).ι.toLRSHom.toShHom).mapIso hF.some ≪≫
    derivedPullbackCompIsoOfScheme (S.modificationChartComplement b).ι _ S.E ≪≫
    (eqToIso (by rw [Category.assoc]))⟩

/-- If `Q|_{b^{-1}(𝐀¹_X)}` is the pullback of `F` and `F|_{X ∖ Z}` is zero, then `Q` vanishes on
the part of the chart lying over `X ∖ Z`. -/
theorem isZero_modificationChartComplement (hS : S.IsZeroOnComplement)
    (hF : Nonempty ((derivedPullback
        (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q ≅
      (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a) ≫
        modificationProjection S.a b).toLRSHom.toShHom).obj S.E)) :
    IsZero ((derivedPullback ((S.modificationChartComplement b).ι ≫
      pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q) := by
  have hfac := S.modificationChartComplement_fac b
  have h₁ := isZero_derivedPullback_of_fac (E := S.E) hfac hS
  exact h₁.of_iso (S.nonempty_iso_modificationChartComplement hF).some

/-- If `Q|_{b^{-1}(𝐀¹_X)}` is the pullback of `F` and `F|_{X ∖ Z}` is finite locally free of rank
`< p` in degree `0`, then so is `Q` on the part of the chart lying over `X ∖ Z`. -/
theorem exists_rankLT_modificationChartComplement
    (hS : S.IsFiniteLocallyFreeOfRankLTOnComplement)
    (hF : Nonempty ((derivedPullback
        (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q ≅
      (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a) ≫
        modificationProjection S.a b).toLRSHom.toShHom).obj S.E)) :
    ∃ M : (S.modificationChartComplement b).toScheme.Modules, IsFiniteLocallyFreeOfRankLT M S.p ∧
      Nonempty ((derivedPullback ((S.modificationChartComplement b).ι ≫
        pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M) := by
  have hfac := S.modificationChartComplement_fac b
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors
    (E := S.E) hfac hS
  exact ⟨M, hM, ⟨(S.nonempty_iso_modificationChartComplement hF).some ≪≫ e⟩⟩

variable (b)

include t in
/-- **Condition (2) of Situation 0GUJ on the modification, the case of `P_p`.** Let `U ⊆ W` be
an open subscheme lying over `X ∖ Z` (for instance `W ∖ W ×_X Z`). If `Q|_{b^{-1}(𝐀¹_X)}` is the
pullback of `F`, `F|_{X ∖ Z}` is zero and `Q|_T` is zero for a closed `T ⊆ W_∞` containing every
point of `W_∞` over `X ∖ Z`, then `Q|_U` is zero. -/
theorem modificationRestriction_of_isZero (U : W.Opens)
    (hU : ∀ w ∈ U, modificationProjection S.a b w ∉ Set.range S.i)
    (hQ : RingedSpace.IsPerfect (X := W.toRingedSpace) Q)
    (hS : S.IsZeroOnComplement)
    (hF : Nonempty ((derivedPullback
        (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q ≅
      (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a) ≫
        modificationProjection S.a b).toLRSHom.toShHom).obj S.E))
    (hT : ∀ w, modificationProjectionAtInfinity S.a b w ∉ Set.range S.i → w ∈ Set.range t)
    (hzero : IsZero ((derivedPullback
      (t ≫ modificationInclusionAtInfinity S.a b).toLRSHom.toShHom).obj Q)) :
    IsZero ((derivedPullback (W.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj Q) := by
  refine isZero_of_forall_mem Q hQ _ fun w hw => ?_
  rcases S.mem_range_affineChart_or_mem_range_infinity b w with ⟨u, rfl⟩ | hinf
  · have hu := S.mem_modificationChartComplement b (hU _ hw)
    refine mem_cohomologyFiniteFreeLocus_of_isZero_fibre Q hQ _ ?_
    have hfib := isZero_derivedPullback_of_fac
      (t := W.fromSpecResidueField (pullback.fst b (projectiveLineAffineChart S.a) u))
      (a := IsOpenImmersion.lift ((S.modificationChartComplement b).ι ≫
        pullback.fst b (projectiveLineAffineChart S.a))
          (W.fromSpecResidueField (pullback.fst b (projectiveLineAffineChart S.a) u)) (by
          rw [Scheme.range_fromSpecResidueField]
          rintro _ rfl
          exact ⟨⟨u, hu⟩, rfl⟩)) (IsOpenImmersion.lift_fac _ _ _)
      (S.isZero_modificationChartComplement hS hF)
    exact hfib
  · obtain ⟨τ, rfl⟩ := S.mem_range_of_mem_range_infinity b t hT (hU w hw) hinf
    refine mem_cohomologyFiniteFreeLocus_of_isZero_fibre Q hQ _ ?_
    exact isZero_derivedPullback_of_range_subset (t ≫ modificationInclusionAtInfinity S.a b) _
      (by rw [Scheme.range_fromSpecResidueField]; exact Set.singleton_subset_iff.2 ⟨τ, rfl⟩)
      hzero

omit [IsClosedImmersion t] in
include t in
/-- **Condition (2) of Situation 0GUJ on the modification, the case of `c_p`.** Let `U ⊆ W` be
an open subscheme lying over `X ∖ Z` (for instance `W ∖ W ×_X Z`). If `Q|_{b^{-1}(𝐀¹_X)}` is the
pullback of `F`, `F|_{X ∖ Z}` is finite locally free of rank `< p` in degree `0` and `Q|_T` is such
a module for a closed `T ⊆ W_∞` containing every point of `W_∞` over `X ∖ Z`, then so is `Q|_U`. -/
theorem modificationRestriction_of_rankLT (U : W.Opens)
    (hU : ∀ w ∈ U, modificationProjection S.a b w ∉ Set.range S.i)
    (hQ : RingedSpace.IsPerfect (X := W.toRingedSpace) Q)
    (hS : S.IsFiniteLocallyFreeOfRankLTOnComplement)
    (hF : Nonempty ((derivedPullback
        (pullback.fst b (projectiveLineAffineChart S.a)).toLRSHom.toShHom).obj Q ≅
      (derivedPullback (pullback.fst b (projectiveLineAffineChart S.a) ≫
        modificationProjection S.a b).toLRSHom.toShHom).obj S.E))
    (hT : ∀ w, modificationProjectionAtInfinity S.a b w ∉ Set.range S.i → w ∈ Set.range t)
    (hrank : ∃ M : T.Modules, IsFiniteLocallyFreeOfRankLT M S.p ∧
      Nonempty ((derivedPullback (t ≫ modificationInclusionAtInfinity S.a b).toLRSHom.toShHom).obj
        Q ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : OXMod.{u, u, u} (W.toRingedSpace.restrict U.isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M S.p ∧ Nonempty ((derivedPullback
        (W.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj Q ≅
          (DerivedCategory.singleFunctor _ 0).obj M) := by
  refine exists_iso_singleFunctor_of_forall_mem Q hQ _ S.p fun w hw => ?_
  rcases S.mem_range_affineChart_or_mem_range_infinity b w with ⟨u, rfl⟩ | hinf
  · have hu := S.mem_modificationChartComplement b (hU _ hw)
    exact mem_cohomologyFiniteFreeLocus_of_rankLT Q hQ _
      (S.exists_rankLT_modificationChartComplement hS hF) ⟨u, hu⟩
  · obtain ⟨τ, rfl⟩ := S.mem_range_of_mem_range_infinity b t hT (hU w hw) hinf
    exact mem_cohomologyFiniteFreeLocus_of_rankLT Q hQ _ hrank τ

variable {b} in
/-- An open subscheme of `W` lying over `X ∖ Z` maps to `X ∖ Z`. -/
theorem range_comp_subset_complementOpens (U : W.Opens)
    (hU : ∀ w ∈ U, modificationProjection S.a b w ∉ Set.range S.i) :
    Set.range (U.ι ≫ modificationProjection S.a b) ⊆ Set.range (S.complementOpens).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  exact hU x.1 x.2

/-- **Condition (2) of Situation 0GUJ for `π^* F`, the case of `P_p`.** If `F|_{X ∖ Z}` is zero, so
is `(π^* F)|_U` for every open `U ⊆ W` lying over `X ∖ Z`. -/
theorem isZero_pullback_restriction (U : W.Opens)
    (hU : ∀ w ∈ U, modificationProjection S.a b w ∉ Set.range S.i) (hS : S.IsZeroOnComplement) :
    IsZero ((derivedPullback (W.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj
      ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E)) :=
  (isZero_derivedPullback_of_fac (E := S.E)
    (IsOpenImmersion.lift_fac (S.complementOpens).ι _ (S.range_comp_subset_complementOpens U hU))
    hS).of_iso (derivedPullbackCompIsoOfScheme U.ι _ S.E)

/-- **Condition (2) of Situation 0GUJ for `π^* F`, the case of `c_p`.** If `F|_{X ∖ Z}` is finite
locally free of rank `< p` in degree `0`, so is `(π^* F)|_U` for every open `U ⊆ W` lying over
`X ∖ Z`. -/
theorem exists_rankLT_pullback_restriction (U : W.Opens)
    (hU : ∀ w ∈ U, modificationProjection S.a b w ∉ Set.range S.i)
    (hS : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    ∃ M : OXMod.{u, u, u} (W.toRingedSpace.restrict U.isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M S.p ∧ Nonempty ((derivedPullback
        (W.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj
          ((derivedPullback (modificationProjection S.a b).toLRSHom.toShHom).obj S.E) ≅
          (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors
    (E := S.E)
    (IsOpenImmersion.lift_fac (S.complementOpens).ι _ (S.range_comp_subset_complementOpens U hU))
    hS
  exact ⟨M, hM, ⟨derivedPullbackCompIsoOfScheme U.ι _ S.E ≪≫ e⟩⟩

end LocalizedSituation

end Stacks.Chow

end
