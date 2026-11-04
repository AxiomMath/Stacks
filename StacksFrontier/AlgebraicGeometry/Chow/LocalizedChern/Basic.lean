module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernData
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CriteriaLocalizedSituation
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupDecalagePerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GraphConstructionTriple
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.DivisorRankStrata
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Preparation

/-!
# The localized classes of the graph construction

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed immersion and let `E` be a perfect object of
`D(𝒪_X)`. Macpherson's graph construction (More on Flatness, Section 0F8Z) produces a proper
morphism `b : W ⟶ 𝐏¹_X` and a perfect object `Q` of `D(𝒪_W)` whose restriction to `X × {0}` is
`E`. The localized classes `P_p(Z ⟶ X, E)` and `c_p(Z ⟶ X, E)` of Stacks 0FB2 are the classes
`P'_p(Q)` and `c'_p(Q)` of Stacks 0F9K for `W`, `b`, `Q` and a closed subscheme `T' ⊆ W_∞`
containing `W_∞ ×_X (X ∖ Z)` on which `Q` is zero, resp. a finite locally free module of rank
`< p` in degree `0`.

This file carries out that construction starting from any closed subscheme `T ⊆ W_∞` with the
properties that Stacks 0F90 (3), (4) assert, following the proof of Stacks 0FB2:

* the cohomology sheaves of `Li^*Q` are finite locally free, so their ranks are locally constant
  on `T`, and `T' ⊆ T` is the open and closed locus where they all vanish, resp. where `H^n`
  vanishes for `n ≠ 0` and `H^0` has rank `< p`;
* on `T'` the object `Q` restricts to zero, resp. to a finite locally free module of rank `< p` in
  degree `0`, because an object of the derived category whose cohomology vanishes is zero, and one
  whose cohomology is concentrated in degree `0` is the cohomology sheaf placed in degree `0`;
* the identities `i_* ∘ P_p(Z ⟶ X, E) = P_p(E)` and `i_* ∘ c_p(Z ⟶ X, E) = c_p(E)` are those of
  Stacks 0F9K together with `Q|_{X × {0}} ≅ E`, clause (2) of Stacks 0F90.

It also proves that the Chern classes of `Q` are defined under the finiteness conditions (a), (b)
and (c) of Situation 0GUJ, the second paragraph of the proof of Stacks 0FB2: if the irreducible
components of `X` are quasi-compact, so are those of `W`, because `W ⟶ X` is proper, and
Stacks 0GUE (3) applies; if `E` is represented by a locally bounded complex of finite locally free
modules, so is `Q`, by Stacks 0F90 (5).

## Main definitions

* `Stacks.Chow.graphZeroLocus`, `Stacks.Chow.graphSmallRankLocus` — the open and closed
  `T' ⊆ T` on which `Q` is zero, resp. finite locally free of rank `< p` in degree `0`.
* `Stacks.Chow.graphPowerSumClass`, `Stacks.Chow.graphChernClass` — the classes
  `P_p(Z ⟶ X, E)`, resp. `c_p(Z ⟶ X, E)`, in `A^p(Z ⟶ X)` attached to `T`.

## Main results

* `Stacks.Chow.properPushforwardChowCohomology_graphPowerSumClass`,
  `Stacks.Chow.properPushforwardChowCohomology_graphChernClass` —
  `i_* ∘ P_p(Z ⟶ X, E) = P_p(E)` and `i_* ∘ c_p(Z ⟶ X, E) = c_p(E)`.
* `Stacks.Chow.mem_range_of_notMem_range_of_isFiniteLocallyFree`,
  `Stacks.Chow.finiteLocallyFreeRank_eq_zero_of_isZero`,
  `Stacks.Chow.finiteLocallyFreeRank_lt_of_isFiniteLocallyFreeOfRank` — clauses (3) and (4) of
  Stacks 0F90 give the hypotheses on `T` the construction uses, and
  `Stacks.Chow.LocalizedSituation.exists_isZero_pullback_homology`,
  `Stacks.Chow.LocalizedSituation.exists_isFiniteLocallyFreeOfRank_pullback_homology` put
  condition (2) of Situation 0GUJ in the form these lemmas use.
* `Stacks.Chow.exists_finiteLocallyFreeRank_homology_eq_zero_of_isPerfect` — the ranks of the
  cohomology sheaves of a perfect object are locally bounded.
* `Stacks.Chow.hasDefinedChernClasses_graphObject_of_isCompact_irreducibleComponents`,
  `Stacks.Chow.hasDefinedChernClasses_graphObject_of_compactSpace`,
  `Stacks.Chow.hasDefinedChernClasses_graphObject_of_isLocallyBoundedFiniteLocallyFree` — the
  Chern classes of `Q` are defined under the finiteness conditions (a), (b), (c) of Situation 0GUJ.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_finiteLocallyFreeRank_eq`
  — a finite locally free module has rank `r` on any open subscheme inside its rank-`r` locus.
* `Stacks.Chow.perfectPowerSum_eq_of_iso` — the power sums `P_p(E)` of a perfect object depend
  only on its isomorphism class.

## Implementation notes

The closed subscheme `T` is an arbitrary scheme with a closed immersion `T ⟶ W_∞`. The hypotheses
on it are the ones the construction consumes: finite local freeness of the sheaves `H^n(Li^*Q)`,
containment of the points of `W_∞` over `X ∖ Z`, and the values of the ranks at the points of `T`
over `X ∖ Z`. The second and third are deduced from clauses (3) and (4) of Stacks 0F90 by the
lemmas of the last section. The ranks are locally bounded because `Li^*Q` is perfect
(`Stacks.Chow.exists_finiteLocallyFreeRank_homology_eq_zero_of_isPerfect`), which is what makes
`T'` open.
Containment is pointwise, as in Stacks 0F9K, rather than scheme-theoretic.

The locus `T'` is an open subscheme of `T` whose underlying set is closed, so `T' ⟶ T ⟶ W_∞` is
a closed immersion. In the rank `< p` case it is the union, over `r < p`, of the loci where the
ranks of the `H^n(Li^*Q)` are those of `𝒪^r` placed in degree `0`.

## References

* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FB5](https://stacks.math.columbia.edu/tag/0FB5)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0F8Z](https://stacks.math.columbia.edu/tag/0F8Z)
* [Stacks Project, Tag 0F90](https://stacks.math.columbia.edu/tag/0F90)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open scoped ZeroObject

universe u

/-- If `g : W → X` is a proper map and every irreducible component of `X` is compact, then every
irreducible component of `W` is compact: the image of a component of `W` is irreducible, hence
contained in a component of `X`, whose preimage is compact; and a component is closed. -/
theorem isCompact_of_mem_irreducibleComponents_of_isProperMap {W X : Type*}
    [TopologicalSpace W] [TopologicalSpace X] {g : W → X} (hg : IsProperMap g)
    (hX : ∀ C ∈ irreducibleComponents X, IsCompact C) :
    ∀ C ∈ irreducibleComponents W, IsCompact C := by
  intro C hC
  obtain ⟨K, hK, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (g '' C)
    (hC.1.image g hg.continuous.continuousOn)
  exact (hg.isCompact_preimage (hX K hK)).of_isClosed_subset
    (isClosed_of_mem_irreducibleComponents C hC) (Set.image_subset_iff.1 hsub)

/-! ### Rank loci of a finite locally free module -/

namespace AlgebraicGeometry.Scheme.Modules

/-- **A finite locally free module restricts to rank `r` along an open immersion into the locus
where its rank is `r`.** Near every point of that locus the module is free of rank `r`, and the
restriction of a free module along an open immersion is free. -/
theorem isFiniteLocallyFreeOfRank_pullback_of_finiteLocallyFreeRank_eq {T Y : Scheme.{u}}
    (M : T.Modules) [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (g : Y ⟶ T) [IsOpenImmersion g] {r : ℕ} (hg : ∀ y, finiteLocallyFreeRank M (g.base y) = r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj M) r := by
  rw [← isFiniteLocallyFreeOfRank_iff]
  refine IsFiniteLocallyFreeOfRank.of_iso ((restrictFunctorIsoPullback g).app M) fun y => ?_
  obtain ⟨V, hyV, -, I, ⟨eI⟩, ⟨e⟩⟩ :=
    exists_free_nbhd_of_mem_rankStratum M r (g.base y) ((mem_rankStratum M).2 (hg y))
  let F := Scheme.Modules.overEquiv (X := T) V
  have hdisc : Limits.PreservesColimitsOfShape (Discrete I) F.functor :=
    Limits.preservesColimitsOfShape_of_discrete F.functor
  have hunit : SheafOfModules.unit (V.toScheme).ringCatSheaf ≅
      F.functor.obj (SheafOfModules.unit (T.ringCatSheaf.over V)) := Iso.refl _
  let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F.functor I hdisc hunit
  let ε : M.restrict V.ι ≅ SheafOfModules.free.{u} (ULift.{u, 0} (Fin r)) :=
    ((Scheme.Modules.overFunctorEquiv (X := T) V).app M).symm ≪≫ F.functor.mapIso e.symm ≪≫
      eFree.symm ≪≫
      (SheafOfModules.freeFunctor (R := (V.toScheme).ringCatSheaf)).mapIso
        (eI.trans Equiv.ulift.symm).toIso
  refine ⟨g ⁻¹ᵁ V, hyV, ⟨?_⟩⟩
  exact ((restrictFunctorComp (g ⁻¹ᵁ V).ι g).app M).symm ≪≫
    ((restrictFunctorCongr (morphismRestrict_ι g V)).app M).symm ≪≫
    (restrictFunctorComp (g ∣_ V) V.ι).app M ≪≫
    (restrictFunctor (g ∣_ V)).mapIso ε ≪≫
    (restrictFreeIso (g ∣_ V) (ULift.{u, 0} (Fin r))).symm

/-- **A finite locally free module restricts to zero along an open immersion into the locus where
its rank is `0`.** -/
theorem isZero_pullback_of_finiteLocallyFreeRank_eq_zero {T Y : Scheme.{u}} (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] (g : Y ⟶ T)
    [IsOpenImmersion g] (hg : ∀ y, finiteLocallyFreeRank M (g.base y) = 0) :
    IsZero ((Scheme.Modules.pullback g).obj M) :=
  @Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRank_zero _ _
    (isFiniteLocallyFreeOfRank_pullback_of_finiteLocallyFreeRank_eq M g hg)

/-- **A finite locally free module restricts to rank `< p` along an open immersion into the locus
where its rank is `< p`.** -/
theorem isFiniteLocallyFreeOfRankLT_pullback_of_finiteLocallyFreeRank_lt {T Y : Scheme.{u}}
    (M : T.Modules) [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (g : Y ⟶ T) [IsOpenImmersion g] {p : ℕ} (hg : ∀ y, finiteLocallyFreeRank M (g.base y) < p) :
    Stacks.Chow.IsFiniteLocallyFreeOfRankLT (X := Y.toRingedSpace)
      ((Scheme.Modules.pullback g).obj M) p := by
  refine ⟨AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme g M hM,
    fun y => ?_⟩
  let r := finiteLocallyFreeRank M (g.base y)
  let U : Y.Opens := g ⁻¹ᵁ rankStratum M r
  refine ⟨U, (mem_rankStratum M).2 rfl, r, hg y, ?_⟩
  have h := isFiniteLocallyFreeOfRank_pullback_of_finiteLocallyFreeRank_eq M (U.ι ≫ g)
    (r := r) fun y' => (mem_rankStratum M).1 (y'.2 : g.base y'.1 ∈ rankStratum M r)
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (((Scheme.Modules.pullbackComp U.ι g).app M).symm ≪≫
      ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y U).app _ ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm) h

/-- **A free module on a nonempty index type over a nonempty scheme is not zero**: the structure
sheaf is a retract of it, and the structure sheaf of a nonempty scheme is not zero, since its
global sections map onto the nonzero local ring at a point. -/
theorem not_isZero_free {Y : Scheme.{u}} (y : Y) {I : Type u} (i : I) :
    ¬ IsZero (SheafOfModules.free.{u} (R := Y.ringCatSheaf) I) := by
  classical
  intro h
  have hunit : IsZero (SheafOfModules.unit Y.ringCatSheaf) := by
    rw [IsZero.iff_id_eq_zero]
    let g := (SheafOfModules.freeHomEquiv (SheafOfModules.unit Y.ringCatSheaf) (I := I)).symm
      fun _ => (SheafOfModules.unit Y.ringCatSheaf).unitHomEquiv (𝟙 _)
    have hfac : SheafOfModules.ιFree i ≫ g = 𝟙 (SheafOfModules.unit Y.ringCatSheaf) := by
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply,
        Equiv.symm_apply_apply]
    rw [← hfac, h.eq_of_src g 0, Limits.comp_zero]
  have h1 : IsZero ((PresheafOfModules.evaluation Y.ringCatSheaf.obj (Opposite.op ⊤)).obj
      ((SheafOfModules.forget Y.ringCatSheaf).obj (SheafOfModules.unit Y.ringCatSheaf))) :=
    Functor.map_isZero _ (Functor.map_isZero _ hunit)
  have hsub : Subsingleton Γ(Y, (⊤ : Y.Opens)) := ModuleCat.subsingleton_of_isZero h1
  have hone : (1 : Y.presheaf.stalk y) = 0 := by
    rw [← map_one (Y.presheaf.germ ⊤ y trivial).hom, Subsingleton.elim (1 : Γ(Y, (⊤ : Y.Opens))) 0,
      map_zero]
  exact one_ne_zero hone

/-- A module which restricts to zero on an open `V` restricts to zero on every open `W ≤ V`. -/
private theorem isZero_pullback_of_le {T : Scheme.{u}} (M : T.Modules) {V W : T.Opens}
    (hWV : W ≤ V) (hV : IsZero ((Scheme.Modules.pullback V.ι).obj M)) :
    IsZero ((Scheme.Modules.pullback W.ι).obj M) :=
  (Functor.map_isZero (Scheme.Modules.pullback (T.homOfLE hWV)) hV).of_iso
    (((Scheme.Modules.pullbackCongr (T.homOfLE_ι hWV)).app M).symm ≪≫
      ((Scheme.Modules.pullbackComp (T.homOfLE hWV) V.ι).app M).symm)

/-- **A finite locally free module has rank `0` at every point of an open on which it
vanishes.** On the part of that open where the rank is `r` the module is free of rank `r`, and a
free module of positive rank on a nonempty scheme is not zero. -/
theorem finiteLocallyFreeRank_eq_zero_of_isZero_pullback {T : Scheme.{u}} (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] (V : T.Opens)
    (hV : IsZero ((Scheme.Modules.pullback V.ι).obj M)) {v : T} (hv : v ∈ V) :
    finiteLocallyFreeRank M v = 0 := by
  by_contra hr
  set r := finiteLocallyFreeRank M v
  let W : T.Opens := V ⊓ rankStratum M r
  have hWV : W ≤ V := inf_le_left
  have h1 := isFiniteLocallyFreeOfRank_pullback_of_finiteLocallyFreeRank_eq M W.ι (r := r)
    fun w => (mem_rankStratum M).1 w.2.2
  have h0 := isZero_pullback_of_le M hWV hV
  rw [← isFiniteLocallyFreeOfRank_iff] at h1
  let w : W.toScheme := ⟨v, hv, rfl⟩
  obtain ⟨U, hU, ⟨e⟩⟩ := h1 w
  exact not_isZero_free (⟨w, hU⟩ : U.toScheme) (⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩ : ULift (Fin r))
    ((Functor.map_isZero (restrictFunctor U.ι) h0).of_iso e.symm)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Objects whose cohomology sheaves are finite locally free -/

section LocallyFreeCohomology

variable {T Y : Scheme.{u}} (g : Y ⟶ T) [IsOpenImmersion g] (K : DerivedCategory T.Modules)
  (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((DerivedCategory.homologyFunctor T.Modules n).obj K))

/-- The cohomology sheaves of the restriction of `K` along an open immersion `g` are the
restrictions of the cohomology sheaves of `K`. -/
def homologyDerivedPullbackOpenImmersionIso (n : ℤ) :
    (DerivedCategory.homologyFunctor Y.Modules n).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj K) ≅
      (Scheme.Modules.pullback g).obj ((DerivedCategory.homologyFunctor T.Modules n).obj K) :=
  have hfl : AlgebraicGeometry.IsFlat g.toLRSHom.toShHom := fun y =>
    AlgebraicGeometry.Flat.stalkMap g y
  have _ : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _ hfl
  have _ : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  Stacks.BlowUpComplexes.homologyDerivedPullbackIso g.toLRSHom.toShHom K n

/-- If `H^n(K)` has rank `0` on the image of the open immersion `g`, then `H^n` of the restriction
of `K` along `g` vanishes. -/
private theorem isZero_homology_derivedPullback_of_rank_eq_zero (n : ℤ)
    (hg : ∀ y : Y, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) (g.base y) = 0) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules n).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g.toLRSHom.toShHom).obj K)) :=
  (@Scheme.Modules.isZero_pullback_of_finiteLocallyFreeRank_eq_zero T Y _ (hH n) g _ hg).of_iso
    (homologyDerivedPullbackOpenImmersionIso g K n)

include hH in
/-- **An object with finite locally free cohomology sheaves restricts to zero along an open
immersion into the locus where all of them have rank `0`.** -/
theorem isZero_derivedPullback_of_finiteLocallyFreeRank_eq_zero
    (hg : ∀ (n : ℤ) (y : Y), @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) (g.base y) = 0) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g.toLRSHom.toShHom).obj K) := by
  have : IsIso (0 : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g.toLRSHom.toShHom).obj K ⟶ 0) :=
    (DerivedCategory.isIso_iff _ _).2 fun n =>
      isIso_of_source_target_iso_zero _
        (isZero_homology_derivedPullback_of_rank_eq_zero g K hH n (hg n)).isoZero
        (Functor.map_isZero _ (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso 0)

include hH in
/-- **An object with finite locally free cohomology sheaves is, after restriction along an open
immersion into the locus where `H^n` has rank `0` for `n ≠ 0` and `H^0` has rank `< p`, a finite
locally free module of rank `< p` placed in degree `0`.** -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback {p : ℕ}
    (hg : ∀ (n : ℤ) (y : Y), n ≠ 0 →
      @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) (g.base y) = 0)
    (hg₀ : ∀ y : Y, @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) (g.base y) < p) :
    ∃ M : Y.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g.toLRSHom.toShHom).obj K ≅ (DerivedCategory.singleFunctor _ 0).obj M) := by
  set L := (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    g.toLRSHom.toShHom).obj K
  have hz : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor Y.Modules n).obj L) :=
    fun n hn => isZero_homology_derivedPullback_of_rank_eq_zero g K hH n fun y => hg n y hn
  have : L.IsGE 0 := (DerivedCategory.isGE_iff L 0).2 fun i hi => hz i hi.ne
  have : L.IsLE 0 := (DerivedCategory.isLE_iff L 0).2 fun i hi => hz i hi.ne'
  obtain ⟨M, ⟨e⟩⟩ := L.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  refine ⟨(Scheme.Modules.pullback g).obj ((DerivedCategory.homologyFunctor T.Modules 0).obj K),
    @Scheme.Modules.isFiniteLocallyFreeOfRankLT_pullback_of_finiteLocallyFreeRank_lt T Y _ (hH 0)
      g _ p hg₀, ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso ?_⟩⟩
  exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm ≪≫
    (DerivedCategory.homologyFunctor Y.Modules 0).mapIso e.symm ≪≫
    homologyDerivedPullbackOpenImmersionIso g K 0

/-- **The ranks of the cohomology sheaves of a perfect object are locally bounded.** Near every
point a perfect object is quasi-isomorphic to a strictly perfect complex, which vanishes outside
a finite range of degrees; there the cohomology sheaves vanish, hence have rank `0`. -/
theorem exists_finiteLocallyFreeRank_homology_eq_zero_of_isPerfect {T : Scheme.{u}}
    (K : DerivedCategory T.Modules) (hK : RingedSpace.IsPerfect (X := T.toRingedSpace) K)
    (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((DerivedCategory.homologyFunctor T.Modules n).obj K)) :
    ∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V,
      @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) v = 0 := by
  intro τ
  obtain ⟨E, hEp, ⟨eK⟩⟩ := hK
  obtain ⟨I, U, hU, hloc⟩ := hEp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU ▸ trivial : τ ∈ iSup U)
  obtain ⟨P, hP, φ, hφ⟩ := hloc i
  obtain ⟨a, b, -, hab⟩ := Stacks.Cohomology.TorAmplitude.exists_bounds_of_isStrictlyPerfect P hP
  refine ⟨U i, hi, Finset.Icc a b, fun n hn v hv => ?_⟩
  have : PreservesFiniteLimits
      (RingedSpace.PseudoCoherence.restrictModules T.toRingedSpace (U i)) :=
    Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (RingedSpace.PseudoCoherence.restrictModules T.toRingedSpace (U i)) :=
    Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteColimits _ _
  have hPn : IsZero (P.homology n) :=
    (P.sc n).isZero_homology_of_isZero_X₂ (hab n (by simpa using hn))
  have hEn : IsZero ((RingedSpace.restrictComplex E (U i)).homology n) :=
    hPn.of_iso (asIso (HomologicalComplex.homologyMap φ n)).symm
  have hR : IsZero ((RingedSpace.PseudoCoherence.restrictModules T.toRingedSpace (U i)).obj
      (E.homology n)) :=
    hEn.of_iso ((E.sc n).mapHomologyIso _).symm
  let E' : CochainComplex T.Modules ℤ := E
  let eK' : DerivedCategory.Q.obj E' ≅ K := eK
  let V : T.Opens := U i
  have hHn : (DerivedCategory.homologyFunctor T.Modules n).obj K ≅ E'.homology n :=
    (DerivedCategory.homologyFunctor T.Modules n).mapIso eK'.symm ≪≫
      (DerivedCategory.homologyFunctorFactors T.Modules n).app E'
  have hpull : IsZero ((Scheme.Modules.pullback V.ι).obj
      ((DerivedCategory.homologyFunctor T.Modules n).obj K)) :=
    hR.of_iso ((Scheme.Modules.pullback V.ι).mapIso hHn ≪≫
      ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict T V).app _ ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm)
  exact @Scheme.Modules.finiteLocallyFreeRank_eq_zero_of_isZero_pullback T _ (hH n) V hpull v hv

end LocallyFreeCohomology

end Stacks.Chow

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)

omit [LocallyOfFiniteType f] in
/-- The object `Q` of the graph construction is perfect: it is the object of Stacks 0F8U for the
morphism of Stacks 0GTY. -/
theorem isPerfect_graphObject :
    RingedSpace.IsPerfect (X := (graphBlowup f E hE).toRingedSpace) (graphObject f E hE) :=
  (graphTriple f E hE).isPerfect_etaDerivedPullbackObject_goodBlowup

/-- **The Chern classes of `Q` are defined when the irreducible components of `X` are
quasi-compact.** Let `X` be locally of finite type over the base of chapter 42 with
quasi-compact irreducible components, and let `E ∈ D(𝒪_X)` be perfect. Then the Chern classes
of the object `Q` of the graph construction for `E` are defined: `W ⟶ X` is proper, so the
irreducible components of `W` are quasi-compact, and Stacks 0GUE (3) applies to the perfect
object `Q`. -/
theorem hasDefinedChernClasses_graphObject_of_isCompact_irreducibleComponents
    (hX : ∀ Z ∈ irreducibleComponents X, IsCompact Z) :
    HasDefinedChernClasses (graphObject f E hE) :=
  hasDefinedChernClasses_of_isCompact_irreducibleComponents C
    (graphBlowupToBase f E hE ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f)
    (isCompact_of_mem_irreducibleComponents_of_isProperMap
      (graphBlowupToBase f E hE ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S)).isProperMap
      hX)
    _ (isPerfect_graphObject C f E hE)

/-- **The Chern classes of `Q` are defined when `X` is quasi-compact.** This is the case `X`
quasi-compact of
`Stacks.Chow.hasDefinedChernClasses_graphObject_of_isCompact_irreducibleComponents`. -/
theorem hasDefinedChernClasses_graphObject_of_compactSpace [CompactSpace X] :
    HasDefinedChernClasses (graphObject f E hE) :=
  hasDefinedChernClasses_graphObject_of_isCompact_irreducibleComponents C f E hE
    fun Z hZ => (isClosed_of_mem_irreducibleComponents Z hZ).isCompact

omit [LocallyOfFiniteType f] in
/-- **The Chern classes of `Q` are defined when `E` is represented by a locally bounded complex
of finite locally free modules.** By Stacks 0F90 (5) the object `Q` of the graph construction is
then represented by a locally bounded complex of finite locally free `𝒪_W`-modules, and the
identity of `W` is an envelope. -/
theorem hasDefinedChernClasses_graphObject_of_isLocallyBoundedFiniteLocallyFree
    (hrep : ∃ ℳ : CochainComplex X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree ℳ ∧
      Nonempty (DerivedCategory.Q.obj ℳ ≅ E)) :
    HasDefinedChernClasses (graphObject f E hE) := by
  obtain ⟨𝒬, h𝒬, ⟨e⟩⟩ := exists_isLocallyBoundedFiniteLocallyFree_graphObject f E hE hrep
  exact hasDefinedChernClasses_of_envelope (𝟙 _) ⟨inferInstance, isCompletelyDecomposed_id _⟩
    _ 𝒬 h𝒬 ⟨(Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso
      (graphBlowup f E hE).toRingedSpace).app _ ≪≫ e.symm⟩

/-! ### Invariance of the Chern classes under isomorphism -/

section Iso

variable {X : Scheme.{u}} {E E' : DerivedCategory X.Modules}

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **`P_p(E)` depends only on the isomorphism class of `E`.** -/
theorem perfectPowerSum_eq_of_iso (hE : HasDefinedChernClasses E)
    (hE' : HasDefinedChernClasses E') (e : E ≅ E') (p : ℕ) :
    perfectPowerSum C sX hE p = perfectPowerSum C sX hE' p :=
  eq_perfectPowerSum C sX hE' (hE.some.congr e) p
    (res_perfectPowerSum_eq_powerSumComplex C sX hE hE.some p)

end Iso

/-! ### The classes attached to a closed subscheme of the fibre at infinity -/

section GraphSubscheme

variable {X Z T : Scheme.{u}} {S : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
  (t : T ⟶ modificationFibreAtInfinity f (graphBlowupToBase f E hE))

/-- The restriction `Li^*Q ∈ D(𝒪_T)` of the object `Q` of the graph construction to a scheme
`i : T ⟶ W_∞` over the fibre at infinity. -/
abbrev graphObjectRestrict : DerivedCategory T.Modules :=
  (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (t ≫ modificationInclusionAtInfinity f (graphBlowupToBase f E hE)).toLRSHom.toShHom).obj
    (graphObject f E hE)

/-- The cohomology sheaves `H^n(Li^*Q)` of the restriction of `Q` to `T`. -/
abbrev graphObjectRestrictHomology (n : ℤ) : T.Modules :=
  (DerivedCategory.homologyFunctor T.Modules n).obj (graphObjectRestrict f E hE t)

variable (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (graphObjectRestrictHomology f E hE t n))

/-- The restriction `Li^*Q` of the object of the graph construction is perfect. -/
theorem isPerfect_graphObjectRestrict :
    RingedSpace.IsPerfect (X := T.toRingedSpace) (graphObjectRestrict f E hE t) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _
    (graphTriple f E hE).isPerfect_etaDerivedPullbackObject_goodBlowup

/-- The ranks of the cohomology sheaves `H^n(Li^*Q)` are locally bounded: near every point all
but finitely many of them have rank `0`, because `Li^*Q` is perfect. -/
theorem graphObjectRestrict_rank_locallyBounded :
    ∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V,
      @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) v = 0 :=
  exists_finiteLocallyFreeRank_homology_eq_zero_of_isPerfect _
    (isPerfect_graphObjectRestrict f E hE t) hH

/-- Restricting `Li^*Q` along `g : Y ⟶ T` is the restriction of `Q` along `(g ≫ t) ≫ i`. -/
private theorem nonempty_iso_derivedPullback_graphObjectRestrict {Y : Scheme.{u}} (g : Y ⟶ T) :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      ((g ≫ t) ≫ modificationInclusionAtInfinity f
        (graphBlowupToBase f E hE)).toLRSHom.toShHom).obj (graphObject f E hE) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj
        (graphObjectRestrict f E hE t)) := by
  rw [Category.assoc]
  exact ⟨((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
    g.toLRSHom.toShHom
    (t ≫ modificationInclusionAtInfinity f (graphBlowupToBase f E hE)).toLRSHom.toShHom).app
      (graphObject f E hE)).symm⟩

/-- **The open and closed locus `T' ⊆ T` on which `Q|_{T'}` is zero**: the locus where every
cohomology sheaf of `Li^*Q` has rank `0`. -/
def graphZeroLocus : T.Opens :=
  ⟨Scheme.Modules.rankStratumSet (graphObjectRestrictHomology f E hE t) hH 0,
    Scheme.Modules.isOpen_rankStratumSet _ hH 0
      (graphObjectRestrict_rank_locallyBounded f E hE t hH)⟩

/-- A point lies in `Stacks.Chow.graphZeroLocus` exactly when every `H^n(Li^*Q)` has rank `0`
there. -/
theorem mem_graphZeroLocus {τ : T} :
    τ ∈ graphZeroLocus f E hE t hH ↔
      ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0 :=
  Scheme.Modules.mem_rankStratumSet

/-- The locus `Stacks.Chow.graphZeroLocus` is closed in `T`. -/
theorem isClosed_graphZeroLocus : IsClosed (graphZeroLocus f E hE t hH : Set T) :=
  Scheme.Modules.isClosed_rankStratumSet _ hH 0

/-- The open and closed `T' ⊆ T` of `Stacks.Chow.graphZeroLocus` is a closed subscheme. -/
instance isClosedImmersion_graphZeroLocus_ι :
    IsClosedImmersion (graphZeroLocus f E hE t hH).ι :=
  IsClosedImmersion.of_isPreimmersion _ <| by
    rw [Scheme.Opens.range_ι]
    exact isClosed_graphZeroLocus f E hE t hH

/-- **The open and closed locus `T' ⊆ T` on which `Q|_{T'}` is a finite locally free module of
rank `< p` in degree `0`**: the locus where `H^n(Li^*Q)` has rank `0` for `n ≠ 0` and `H^0(Li^*Q)`
has rank `< p`. -/
def graphSmallRankLocus (p : ℕ) : T.Opens :=
  ⟨⋃ r ∈ Finset.range p,
      Scheme.Modules.rankStratumSet (graphObjectRestrictHomology f E hE t) hH (Pi.single 0 r),
    isOpen_biUnion fun _ _ => Scheme.Modules.isOpen_rankStratumSet _ hH _
      (graphObjectRestrict_rank_locallyBounded f E hE t hH)⟩

/-- A point lies in `Stacks.Chow.graphSmallRankLocus` exactly when `H^n(Li^*Q)` has rank `0`
there for `n ≠ 0` and `H^0(Li^*Q)` has rank `< p` there. -/
theorem mem_graphSmallRankLocus {p : ℕ} {τ : T} :
    τ ∈ graphSmallRankLocus f E hE t hH p ↔
      (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
        @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p := by
  change τ ∈ ⋃ r ∈ Finset.range p, _ ↔ _
  simp only [Set.mem_iUnion, Finset.mem_range, Scheme.Modules.mem_rankStratumSet]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨fun n hn => (h n).trans (by simp [hn]), ?_⟩
    simpa [h 0] using hr
  · rintro ⟨h, h₀⟩
    refine ⟨_, h₀, fun n => ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hn, h n hn]

/-- The locus `Stacks.Chow.graphSmallRankLocus` is closed in `T`. -/
theorem isClosed_graphSmallRankLocus (p : ℕ) :
    IsClosed (graphSmallRankLocus f E hE t hH p : Set T) :=
  isClosed_biUnion_finset fun _ _ => Scheme.Modules.isClosed_rankStratumSet _ hH _

/-- The open and closed `T' ⊆ T` of `Stacks.Chow.graphSmallRankLocus` is a closed subscheme. -/
instance isClosedImmersion_graphSmallRankLocus_ι (p : ℕ) :
    IsClosedImmersion (graphSmallRankLocus f E hE t hH p).ι :=
  IsClosedImmersion.of_isPreimmersion _ <| by
    rw [Scheme.Opens.range_ι]
    exact isClosed_graphSmallRankLocus f E hE t hH p

/-- `Q` restricts to zero on the locus `T'` of `Stacks.Chow.graphZeroLocus`. -/
theorem isZero_derivedPullback_graphZeroLocus :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (((graphZeroLocus f E hE t hH).ι ≫ t) ≫
        modificationInclusionAtInfinity f (graphBlowupToBase f E hE)).toLRSHom.toShHom).obj
      (graphObject f E hE)) := by
  exact (isZero_derivedPullback_of_finiteLocallyFreeRank_eq_zero
    (graphZeroLocus f E hE t hH).ι (graphObjectRestrict f E hE t) hH
      fun n y => (mem_graphZeroLocus f E hE t hH).1 y.2 n).of_iso
    (nonempty_iso_derivedPullback_graphObjectRestrict f E hE t _).some

/-- `Q` restricts to a finite locally free module of rank `< p` in degree `0` on the locus `T'`
of `Stacks.Chow.graphSmallRankLocus`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus (p : ℕ) :
    ∃ M : (graphSmallRankLocus f E hE t hH p).toScheme.Modules,
      IsFiniteLocallyFreeOfRankLT M p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (((graphSmallRankLocus f E hE t hH p).ι ≫ t) ≫
            modificationInclusionAtInfinity f (graphBlowupToBase f E hE)).toLRSHom.toShHom).obj
          (graphObject f E hE) ≅ (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback
    (graphSmallRankLocus f E hE t hH p).ι (graphObjectRestrict f E hE t) hH (p := p)
    (fun n y hn => ((mem_graphSmallRankLocus f E hE t hH).1 y.2).1 n hn)
    fun y => ((mem_graphSmallRankLocus f E hE t hH).1 y.2).2
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (nonempty_iso_derivedPullback_graphObjectRestrict f E hE t _).some ≪≫ e

end GraphSubscheme

/-! ### The classes `P_p(Z ⟶ X, E)` and `c_p(Z ⟶ X, E)` attached to `T` -/

section GraphClasses

variable (C : ChowSituation.{u}) {X Z T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
  (z : Z ⟶ X) [IsClosedImmersion z]
  (t : T ⟶ modificationFibreAtInfinity f (graphBlowupToBase f E hE)) [IsClosedImmersion t]
  (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (graphObjectRestrictHomology f E hE t n))
  (hQ : HasDefinedChernClasses (graphObject f E hE)) (p : ℕ)
  (hT : ∀ w, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) w ∉ Set.range z →
    w ∈ Set.range t)

include hT in
omit [LocallyOfFiniteType f] [IsClosedImmersion z] [IsClosedImmersion t] in
/-- Every point of `W_∞` over `X ∖ Z` lies in the locus `T'` of `Stacks.Chow.graphZeroLocus`, if
it lies in `T` and the cohomology sheaves of `Li^*Q` have rank `0` at the points of `T` over
`X ∖ Z`. -/
theorem mem_range_graphZeroLocus
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) :
    ∀ w, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) w ∉ Set.range z →
      w ∈ Set.range ((graphZeroLocus f E hE t hH).ι ≫ t) := by
  intro w hw
  obtain ⟨τ, rfl⟩ := hT w hw
  exact ⟨⟨τ, (mem_graphZeroLocus f E hE t hH).2 (hrk τ hw)⟩, rfl⟩

include hT in
omit [LocallyOfFiniteType f] [IsClosedImmersion z] [IsClosedImmersion t] in
/-- Every point of `W_∞` over `X ∖ Z` lies in the locus `T'` of
`Stacks.Chow.graphSmallRankLocus`, if it lies in `T` and at the points of `T` over `X ∖ Z` the
sheaf `H^n(Li^*Q)` has rank `0` for `n ≠ 0` and `H^0(Li^*Q)` has rank `< p`. -/
theorem mem_range_graphSmallRankLocus
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p) :
    ∀ w, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) w ∉ Set.range z →
      w ∈ Set.range ((graphSmallRankLocus f E hE t hH p).ι ≫ t) := by
  intro w hw
  obtain ⟨τ, rfl⟩ := hT w hw
  exact ⟨⟨τ, (mem_graphSmallRankLocus f E hE t hH).2 (hrk τ hw)⟩, rfl⟩

include hT in
/-- **The class `P_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)` attached to a closed subscheme `T ⊆ W_∞`.** Let
`b : W ⟶ 𝐏¹_X` and `Q` be the graph construction for the perfect object `E`, assume the Chern
classes of `Q` are defined, and let `i : T ⟶ W_∞` be a closed immersion such that the cohomology
sheaves of `Li^*Q` are finite locally free, every point of `W_∞` over `X ∖ Z` lies in `T`, and at
the points of `T` over `X ∖ Z` all of these sheaves have rank `0`. The class is `P'_p(Q)` of Stacks
0F9K for `W`, `b`, `Q` and the open and closed `T' ⊆ T` where all of them have rank `0`
(`Stacks.Chow.graphZeroLocus`), on which `Q` restricts to zero. -/
def graphPowerSumClass
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) :
    BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p :=
  modificationPowerSum C f (graphBlowupToBase f E hE) (isIso_pullback_snd_graphBlowupToBase f E hE)
    z ((graphZeroLocus f E hE t hH).ι ≫ t) hQ p
    (mem_range_graphZeroLocus C f E hE z t hH hT hrk)
    (isZero_derivedPullback_graphZeroLocus f E hE t hH)

include hT in
/-- **The class `c_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)` attached to a closed subscheme `T ⊆ W_∞`.** As
`Stacks.Chow.graphPowerSumClass`, but at the points of `T` over `X ∖ Z` the sheaf `H^n(Li^*Q)` is
required to have rank `0` for `n ≠ 0` and `H^0(Li^*Q)` rank `< p`. The class is `c'_p(Q)` of
Stacks 0F9K for `W`, `b`, `Q` and the open and closed `T' ⊆ T` where these ranks are attained
(`Stacks.Chow.graphSmallRankLocus`), on which `Q` restricts to a finite locally free module of
rank `< p` in degree `0`. -/
def graphChernClass
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p) :
    BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p :=
  modificationChernClass C f (graphBlowupToBase f E hE)
    (isIso_pullback_snd_graphBlowupToBase f E hE) z ((graphSmallRankLocus f E hE t hH p).ι ≫ t)
    hQ p (mem_range_graphSmallRankLocus C f E hE z t hH p hT hrk)
    (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_graphSmallRankLocus f E hE t hH p)

/-- **`i_* ∘ P_p(Z ⟶ X, E) = P_p(E)`** for the class `Stacks.Chow.graphPowerSumClass`, as
bivariant classes on `X`, with `∘` the pushforward of Stacks 0EPK. This is Stacks 0F9K together
with `Q|_{X × {0}} ≅ E`, clause (2) of Stacks 0F90. -/
theorem properPushforwardChowCohomology_graphPowerSumClass
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z → ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0)
    (hE' : HasDefinedChernClasses E) :
    properPushforwardChowCohomology C f (z ≫ f) z rfl
        (graphPowerSumClass C f E hE z t hH hQ p hT hrk) =
      perfectPowerSumComponent C f hE' p := by
  obtain ⟨e⟩ := nonempty_derivedPullback_modificationSectionAtZero_graphObject f E hE
  rw [graphPowerSumClass, properPushforwardChowCohomology_modificationPowerSum]
  unfold perfectPowerSumComponent
  rw [perfectPowerSum_eq_of_iso C f _ hE' e p]

/-- **`i_* ∘ c_p(Z ⟶ X, E) = c_p(E)`** for the class `Stacks.Chow.graphChernClass`, as bivariant
classes on `X`, with `∘` the pushforward of Stacks 0EPK. This is Stacks 0F9K together with
`Q|_{X × {0}} ≅ E`, clause (2) of Stacks 0F90. -/
theorem properPushforwardChowCohomology_graphChernClass
    (hrk : ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉
      Set.range z →
        (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
          @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p)
    (hE' : HasDefinedChernClasses E) :
    properPushforwardChowCohomology C f (z ≫ f) z rfl
        (graphChernClass C f E hE z t hH hQ p hT hrk) =
      perfectChernClass C f hE' p := by
  obtain ⟨e⟩ := nonempty_derivedPullback_modificationSectionAtZero_graphObject f E hE
  rw [graphChernClass, properPushforwardChowCohomology_modificationChernClass,
    perfectChernClass_congr C f _ hE' e]

end GraphClasses

/-! ### From clauses (3) and (4) of Stacks 0F90 to the hypotheses on `T` -/

section GraphClauses

variable {X Z T S : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (z : Z ⟶ X)
  (t : T ⟶ modificationFibreAtInfinity f (graphBlowupToBase f E hE))
  (hH : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (graphObjectRestrictHomology f E hE t n))

/-- **Clause (3) of Stacks 0F90, set-theoretically, gives `T ⊇ W_∞ ×_X (X ∖ Z)`.** If every point
of `W_∞` lying over a point near which all cohomology sheaves of `E` are finite locally free lies
in `T`, and near every point of `X ∖ Z` all cohomology sheaves of `E` are finite locally free,
then every point of `W_∞` over `X ∖ Z` lies in `T`. -/
theorem mem_range_of_notMem_range_of_isFiniteLocallyFree
    (h3 : ∀ (w) (V : X.Opens),
      modificationProjectionAtInfinity f (graphBlowupToBase f E hE) w ∈ V →
      (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules n).obj E))) →
      w ∈ Set.range t)
    (hEZ : ∀ x ∉ Set.range z, ∃ V : X.Opens, x ∈ V ∧ ∀ n : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules n).obj E))) :
    ∀ w, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) w ∉ Set.range z →
      w ∈ Set.range t := fun w hw => by
  obtain ⟨V, hV, hfree⟩ := hEZ _ hw
  exact h3 w V hV hfree

/-- A zero module is finite locally free. -/
private theorem isFiniteLocallyFree_of_isZero {Y : Scheme.{u}} {M : Y.Modules} (hM : IsZero M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
  have := isFiniteLocallyFreeOfRank_zero_of_isZero hM
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 0

/-- **Clause (4) of Stacks 0F90 gives rank `0` over the locus where `E` vanishes.** If the rank of
`H^n(Li^*Q)` at a point of `T` is the rank of `H^n(E)` near its image in `X` whenever all
cohomology sheaves of `E` are finite locally free there, and near every point of `X ∖ Z` all
cohomology sheaves of `E` vanish, then all cohomology sheaves of `Li^*Q` have rank `0` at the
points of `T` over `X ∖ Z`. -/
theorem finiteLocallyFreeRank_eq_zero_of_isZero
    (h4 : ∀ (τ : T) (V : X.Opens) (n : ℤ) (r : ℕ),
      modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∈ V →
      (∀ m : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules m).obj E))) →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules n).obj E))
        r →
      @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = r)
    (hEZ : ∀ x ∉ Set.range z, ∃ V : X.Opens, x ∈ V ∧ ∀ n : ℤ,
      IsZero ((Scheme.Modules.pullback V.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj E))) :
    ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉ Set.range z →
      ∀ n : ℤ, @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0 := fun τ hτ n => by
  obtain ⟨V, hV, hzero⟩ := hEZ _ hτ
  exact h4 τ V n 0 hV (fun m => isFiniteLocallyFree_of_isZero (hzero m))
    (isFiniteLocallyFreeOfRank_zero_of_isZero (hzero n))

/-- **Clause (4) of Stacks 0F90 gives small rank over the locus where `E` is a finite locally free
module of rank `< p` in degree `0`.** If the rank of `H^n(Li^*Q)` at a point of `T` is the rank of
`H^n(E)` near its image in `X` whenever all cohomology sheaves of `E` are finite locally free
there, and near every point of `X ∖ Z` the sheaf `H^0(E)` is finite locally free of some rank `< p`
and the other cohomology sheaves of `E` vanish, then at the points of `T` over `X ∖ Z` the sheaf
`H^n(Li^*Q)` has rank `0` for `n ≠ 0` and `H^0(Li^*Q)` has rank `< p`. -/
theorem finiteLocallyFreeRank_lt_of_isFiniteLocallyFreeOfRank {p : ℕ}
    (h4 : ∀ (τ : T) (V : X.Opens) (n : ℤ) (r : ℕ),
      modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∈ V →
      (∀ m : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules m).obj E))) →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules n).obj E))
        r →
      @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = r)
    (hEZ : ∀ x ∉ Set.range z, ∃ V : X.Opens, x ∈ V ∧ (∃ r < p,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules 0).obj E))
        r) ∧ ∀ n : ℤ, n ≠ 0 →
      IsZero ((Scheme.Modules.pullback V.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj E))) :
    ∀ τ : T, modificationProjectionAtInfinity f (graphBlowupToBase f E hE) (t τ) ∉ Set.range z →
      (∀ n : ℤ, n ≠ 0 → @Scheme.Modules.finiteLocallyFreeRank T _ (hH n) τ = 0) ∧
        @Scheme.Modules.finiteLocallyFreeRank T _ (hH 0) τ < p := fun τ hτ => by
  obtain ⟨V, hV, ⟨r, hr, hrank⟩, hzero⟩ := hEZ _ hτ
  have hfree : ∀ m : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules m).obj E)) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
    · exact isFiniteLocallyFree_of_isZero (hzero m hm)
  exact ⟨fun n hn => h4 τ V n 0 hV hfree (isFiniteLocallyFreeOfRank_zero_of_isZero (hzero n hn)),
    (h4 τ V 0 r hV hfree hrank).trans_lt hr⟩

end GraphClauses

/-! ### The restriction hypothesis of Situation 0GUJ near a point -/

section SituationRestriction

variable {X : Scheme.{u}} (U : X.Opens) (E : DerivedCategory X.Modules)

/-- If `E` restricts to zero on an open `U`, then so do all of its cohomology sheaves. -/
theorem isZero_pullback_homology_of_isZero
    (h : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj E)) (n : ℤ) :
    IsZero ((Scheme.Modules.pullback U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj E)) :=
  (Functor.map_isZero (DerivedCategory.homologyFunctor U.toScheme.Modules n) h).of_iso
    (homologyDerivedPullbackOpenImmersionIso U.ι E n).symm

/-- If `E` restricts on an open `U` to a finite locally free module of rank `< p` placed in
degree `0`, then every point of `U` has an open neighbourhood `V ≤ U` on which `H^0(E)` is finite
locally free of some rank `< p` and the other cohomology sheaves of `E` vanish. -/
theorem exists_isFiniteLocallyFreeOfRank_pullback_homology_of_iso_single {p : ℕ}
    (h : ∃ M : OXMod.{u, u, u} (X.toRingedSpace.restrict U.isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (X.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj E ≅
            (DerivedCategory.singleFunctor _ 0).obj M))
    {x : X} (hx : x ∈ U) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
      (∃ r < p, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj ((DerivedCategory.homologyFunctor X.Modules 0).obj E))
        r) ∧
      ∀ n : ℤ, n ≠ 0 → IsZero ((Scheme.Modules.pullback V.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj E)) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := h
  let M' : U.toScheme.Modules := M
  let e' : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback U.ι.toLRSHom.toShHom).obj E ≅
      (DerivedCategory.singleFunctor _ 0).obj M' := e
  have eH : ∀ n : ℤ, (Scheme.Modules.pullback U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj E) ≅
        (DerivedCategory.homologyFunctor U.toScheme.Modules n).obj
          ((DerivedCategory.singleFunctor _ 0).obj M') := fun n =>
    (homologyDerivedPullbackOpenImmersionIso U.ι E n).symm ≪≫
      (DerivedCategory.homologyFunctor U.toScheme.Modules n).mapIso e'
  have hz : ∀ n : ℤ, n ≠ 0 → IsZero ((Scheme.Modules.pullback U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj E)) := by
    intro n hn
    refine IsZero.of_iso ?_ (eH n)
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact ((DerivedCategory.singleFunctor _ 0).obj M').isZero_of_isGE 0 n hn
    · exact ((DerivedCategory.singleFunctor _ 0).obj M').isZero_of_isLE 0 n hn
  have e0 : (Scheme.Modules.pullback U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules 0).obj E) ≅ M' :=
    eH 0 ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M'
  obtain ⟨U₀, hxU₀, r, hr, hU₀⟩ := hM.2 ⟨x, hx⟩
  let U' : U.toScheme.Opens := U₀
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U'.ι).obj ((Scheme.Modules.pullback U.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules 0).obj E))) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict U.toScheme U').app
        M' ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U'.ι).app M') ≪≫
          (Scheme.Modules.pullback U'.ι).mapIso e0.symm) hU₀
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (U'.ι ≫ U.ι)).obj
        ((DerivedCategory.homologyFunctor X.Modules 0).obj E)) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullbackComp U'.ι U.ι).app _) h1
  let V : X.Opens := U.ι ''ᵁ U'
  have hVU : V ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  refine ⟨V, ⟨⟨x, hx⟩, hxU₀, rfl⟩, hVU, ⟨r, hr, ?_⟩, fun n hn => ?_⟩
  · exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullbackComp (U.ι.isoImage U').inv (U'.ι ≫ U.ι)).app _ ≪≫
        (Scheme.Modules.pullbackCongr (U.ι.isoImage_inv_ι U')).app _)
      (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (U.ι.isoImage U').inv _ r)
  · exact Scheme.Modules.isZero_pullback_of_le _ hVU (hz n hn)

end SituationRestriction

/-- **Situation 0GUJ (2), zero case, near a point.** If `E` restricts to zero on `X ∖ Z`, then
every point of `X ∖ Z` has an open neighbourhood on which all cohomology sheaves of `E`
vanish. -/
theorem LocalizedSituation.exists_isZero_pullback_homology (S : LocalizedSituation.{u})
    (h : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (S.X.toRingedSpace.ofRestrict (⟨(Set.range S.i.base)ᶜ,
        S.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : S.X.Opens).isOpenEmbedding)).obj
        S.E)) :
    ∀ x ∉ Set.range S.i, ∃ V : S.X.Opens, x ∈ V ∧ ∀ n : ℤ,
      IsZero ((Scheme.Modules.pullback V.ι).obj
        ((DerivedCategory.homologyFunctor S.X.Modules n).obj S.E)) :=
  fun _ hx => ⟨_, hx, isZero_pullback_homology_of_isZero _ S.E h⟩

/-- **Situation 0GUJ (2), rank `< p` case, near a point.** If `E` restricts on `X ∖ Z` to a
finite locally free module of rank `< p` placed in degree `0`, then every point of `X ∖ Z` has an
open neighbourhood on which `H^0(E)` is finite locally free of some rank `< p` and the other
cohomology sheaves of `E` vanish. -/
theorem LocalizedSituation.exists_isFiniteLocallyFreeOfRank_pullback_homology
    (S : LocalizedSituation.{u})
    (h : ∃ M : OXMod.{u, u, u} (S.X.toRingedSpace.restrict (⟨(Set.range S.i.base)ᶜ,
        S.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : S.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M S.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (S.X.toRingedSpace.ofRestrict (⟨(Set.range S.i.base)ᶜ,
            S.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
              S.X.Opens).isOpenEmbedding)).obj S.E ≅
            (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∀ x ∉ Set.range S.i, ∃ V : S.X.Opens, x ∈ V ∧
      (∃ r < S.p, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj
          ((DerivedCategory.homologyFunctor S.X.Modules 0).obj S.E)) r) ∧
      ∀ n : ℤ, n ≠ 0 → IsZero ((Scheme.Modules.pullback V.ι).obj
        ((DerivedCategory.homologyFunctor S.X.Modules n).obj S.E)) := fun _ hx => by
  obtain ⟨V, hxV, -, hrank, hzero⟩ :=
    exists_isFiniteLocallyFreeOfRank_pullback_homology_of_iso_single _ S.E h hx
  exact ⟨V, hxV, hrank, hzero⟩

end Stacks.Chow

end
