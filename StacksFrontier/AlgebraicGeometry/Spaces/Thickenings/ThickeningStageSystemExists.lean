module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartImageStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningStageSystem

/-!
# Finite-order stages of a thickening of an affine algebraic space exist

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`G ⊆ X` be a thickening whose underlying algebraic space is affine.  This file produces an
`AlgebraicGeometry.Space.ThickeningStageSystem` for `G ⊆ X`: closed subspaces `G ⊆ H_i ⊆ X`, each
a finite-order thickening of `X`, whose chart ideals on one affine surjective étale chart
exhaust that of `G`.

The ideal of `G` is locally nil but need not be nilpotent, and the source (Stacks 07VS, via
Stacks 0829) would write it as the union of its finite type subideals.  What is needed here is
weaker — nilpotent subideals — and these are produced directly on a chart, with no
quasi-coherence on the small étale site.

1. `X` has an affine surjective étale chart `φ : h_V ⟶ X`, and `R = V ×_X V` is affine
   (`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/AffineChartOfAffineThickening.lean`).
   Write `t s : R ⟶ V` for the projections and `N ⊆ Γ(V)` for the ideal of `G ×_X V`.
2. `N` is nil, because `G ×_X V ⟶ V` is a thickening of schemes and `V` is affine; and
   `s♯(N) · Γ(R) = t♯(N) · Γ(R)`, both being the ideal of `G ×_X R`.
3. For a finite subset `F ⊆ N` let `H_F` be the scheme-theoretic image of
   `V(F) ⟶ V ⟶ X`.  Its chart ideal on `V` is `K_F = s♯⁻¹(t♯(F) · Γ(R))`
   (`AlgebraicGeometry.Space.definingIdealAt_schemeTheoreticImage_chart`, by Stacks 082Z), and
   `K_F ⊆ (F) ⊆ N`.  So `G ⊆ H_F`, and `K_F` is nilpotent because `(F)` is a finitely generated
   nil ideal; hence `H_F` is a finite-order thickening of `X`
   (`AlgebraicGeometry.Space.isNthOrderThickening_of_chartKer_pow_eq_bot`).
4. For `n ∈ N`, `s♯ n ∈ t♯(N) · Γ(R)` is a finite combination of elements `t♯ n_j`, so
   `n ∈ K_F` for `F = {n_j}`.  Hence the `K_F` exhaust `N`.

## Main results

* `AlgebraicGeometry.Space.nonempty_thickeningStageSystem`: a thickening of an affine algebraic
  space admits finite-order stages.

## References

* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

/-- **A function killed by a surjective morphism into a quasi-compact scheme is nilpotent.**
Its basic open has empty preimage, hence is empty. -/
theorem Scheme.isNilpotent_of_appTop_eq_zero_of_surjective {Z Y : Scheme.{u}} [CompactSpace Y]
    (i : Z ⟶ Y) (hi : Function.Surjective i) {x : Γ(Y, ⊤)} (hx : i.appTop x = 0) :
    IsNilpotent x := by
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot]
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨z, rfl⟩ := hi y
  have hz : z ∈ i ⁻¹ᵁ Y.basicOpen x := hy
  rw [Scheme.preimage_basicOpen_top, hx, Scheme.basicOpen_zero] at hz
  simp at hz

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed subscheme of an affine object of the site is an object of the site.** For an
ideal `J` of global functions on an object `V` with affine underlying scheme, there is an
object `Z` with a morphism `ν : Z ⟶ V` which is a closed immersion of schemes with ideal `J`.
The closed subscheme `V(J)` is of finite type and quasi-compact over `V`, so it lies in the
site. -/
theorem exists_siteObject_ofIdealTop {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    ∃ (Z : BigFppfOver B S hS) (ν : Z ⟶ V),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ν) ∧
        RingHom.ker ((BigFppfOver.toScheme B S hS).map ν).appTop.hom = J := by
  set ι := (Scheme.IdealSheafData.ofIdealTop J).subschemeι
  obtain ⟨Z, ν, e, hν⟩ := exists_siteObject_toScheme_map_eq B S hS
    (contains_of_locallyOfFiniteType_of_quasiCompact B S hS ι) ι
  refine ⟨Z, ν, ?_, ?_⟩
  · rw [hν]
    infer_instance
  · have h := Scheme.ker_of_isAffine ((BigFppfOver.toScheme B S hS).map ν)
    rw [hν, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι] at h
    rw [hν]
    exact (Scheme.IdealSheafData.equivOfIsAffine.symm.injective h).symm

/-- **A thickening of an affine algebraic space admits finite-order stages.** Let `X` be an
algebraic space over `S` and let `G ⊆ X` be a thickening whose underlying algebraic space is
affine.  Then there are an affine surjective étale chart `φ : h_V ⟶ X` and a directed antitone
family of closed subspaces `G ⊆ H_i ⊆ X`, each a finite-order thickening of `X`, whose chart
ideals on `V` have supremum the chart ideal of `G`.

The stages are the scheme-theoretic images `H_F` of `V(F) ⟶ V ⟶ X` for the finite subsets
`F` of the ideal `N` of `G ×_X V`, ordered by inclusion.  With `t s : R ⟶ V` the projections of
the affine scheme `R = V ×_X V`, the chart ideal of `H_F` is `K_F = s♯⁻¹(t♯(F) · Γ(R))`, which
lies between `0` and `(F) ⊆ N`; `(F)` is nilpotent, being finitely generated and nil.  The
`K_F` exhaust `N` because `s♯(N) · Γ(R) = t♯(N) · Γ(R)`. -/
theorem nonempty_thickeningStageSystem (X : AlgebraicSpaces B S hS)
    (G : ClosedSubspaces B S hS X.1) (hG : IsThickening B S hS X G.1)
    (hGaff : IsAffineSpace B S hS G.1.toFunctor) :
    Nonempty (ThickeningStageSystem B S hS X G) := by
  classical
  set F := BigFppfOver.toScheme B S hS with hF
  -- The chart and its kernel pair.
  obtain ⟨V, φ, hV, hs, he⟩ :=
    exists_affine_surjective_etale_chart_of_isThickening B S hS hG hGaff
  have hrep : yoneda.relativelyRepresentable φ := he.rep
  set R := hrep.pullback φ
  set t := hrep.fst' φ
  set s := hrep.snd φ
  have hpb : IsPullback (yoneda.map t) (yoneda.map s) φ φ := hrep.isPullback' φ
  have hR : IsAffine (F.obj R) :=
    isAffine_of_isPullback_of_isThickening B S hS hG hGaff hV φ t s hpb
  have _ := hV
  have _ := hR
  set U := chartOfSurjectiveEtale B S hS X he
  have _ : IsAffine (F.obj U.1.left) := hV
  have htop : ∀ a : Ideal Γ(F.obj V, ⊤),
      (Scheme.IdealSheafData.ofIdealTop a).ideal ⟨⊤, isAffineOpen_top _⟩ = a := fun a =>
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply a
  have hofmono : ∀ a b : Ideal Γ(F.obj V, ⊤), a ≤ b →
      Scheme.IdealSheafData.ofIdealTop a ≤ Scheme.IdealSheafData.ofIdealTop b := fun a b h =>
    (map_le_map_iff (Scheme.IdealSheafData.equivOfIsAffine (X := F.obj V)).symm).2 h
  -- The ideal `N` of `G` on the chart.
  set N : Ideal Γ(F.obj V, ⊤) := RingHom.ker (F.map (G.2.2.rep.snd φ)).appTop.hom with hN
  have hGker : chartKer B S hS X G φ = Scheme.IdealSheafData.ofIdealTop N :=
    Scheme.ker_of_isAffine _
  -- `N` is nil.
  have hnil : N ≤ nilradical _ := by
    intro x hx
    have hsurjG : (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) F).presheaf G.1.ι :=
      (surjective_iff_pointsMap_surjective B S hS hG.1.1 X.property G.1.ι hG.1.2.rep).2 hG.2
    have hsj : Surjective (F.map (G.2.2.rep.snd φ)) :=
      hsurjG.property φ _ _ (G.2.2.rep.isPullback φ)
    exact Scheme.isNilpotent_of_appTop_eq_zero_of_surjective _ hsj.surj hx
  -- `s♯(N) · Γ(R) = t♯(N) · Γ(R)`.
  have hkey : N.map (F.map s).appTop.hom = N.map (F.map t).appTop.hom := by
    have h1 := comap_chartKer B S hS X G φ t (yoneda.map t ≫ φ) rfl
    have h2 := comap_chartKer B S hS X G φ s (yoneda.map t ≫ φ) hpb.w.symm
    rw [hGker, Stacks.AlgebraicGeometry.comap_ofIdealTop] at h1 h2
    exact Scheme.IdealSheafData.equivOfIsAffine.symm.injective (h2.trans h1.symm)
  -- The closed subschemes `V(J)` of the chart and their images in `X`.
  choose Z ν hνci hνker using fun J : Ideal Γ(F.obj V, ⊤) =>
    exists_siteObject_ofIdealTop B S hS (V := V) J
  set K : Ideal Γ(F.obj V, ⊤) → Ideal Γ(F.obj V, ⊤) := fun J =>
    (J.map (F.map t).appTop.hom).comap (F.map s).appTop.hom with hK
  have hstage : ∀ J, chartKer B S hS X
      (schemeTheoreticImage B S hS (yoneda.map (ν J) ≫ φ) X.2) φ =
        Scheme.IdealSheafData.ofIdealTop (K J) := by
    intro J
    have _ := hνci J
    have h := definingIdealAt_schemeTheoreticImage_chart B S hS hV hR hs he hpb (ν J)
    rw [hνker J] at h
    exact (ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS X _ U).trans (congrArg _ h)
  have hK_le : ∀ J, K J ≤ J := comap_map_le_of_isPullback B S hS hpb
  have hK_mono : Monotone K := fun J J' h => Ideal.comap_mono (Ideal.map_mono h)
  -- The index: finite subsets of `N`.
  let Ind := {T : Finset Γ(F.obj V, ⊤) // (↑T : Set Γ(F.obj V, ⊤)) ⊆ N}
  have hdirI : IsDirected Ind (· ≤ ·) := ⟨fun a b => ⟨⟨a.1 ∪ b.1, by
    rw [Finset.coe_union]; exact Set.union_subset a.2 b.2⟩,
    Finset.subset_union_left, Finset.subset_union_right⟩⟩
  have hneI : Nonempty Ind := ⟨⟨∅, by simp⟩⟩
  let J : Ind → Ideal Γ(F.obj V, ⊤) := fun i => Ideal.span (↑i.1 : Set Γ(F.obj V, ⊤))
  have hJ_mono : Monotone J := fun i j h => Ideal.span_mono (Finset.coe_subset.2 h)
  have hJ_le : ∀ i, J i ≤ N := fun i => Ideal.span_le.2 i.2
  let stage : Ind → ClosedSubspaces B S hS X.1 := fun i =>
    schemeTheoreticImage B S hS (yoneda.map (ν (J i)) ≫ φ) X.2
  have hchart : ∀ i, chartKer B S hS X (stage i) φ =
      Scheme.IdealSheafData.ofIdealTop (K (J i)) := fun i => hstage (J i)
  have hle_of : ∀ Z W : ClosedSubspaces B S hS X.1,
      chartKer B S hS X W φ ≤ chartKer B S hS X Z φ → Z.1 ≤ W.1 := fun Z W h =>
    le_of_etaleChartKer_le_of_chart B S hS X Z W U hs h
  have hle : ∀ i, G.1 ≤ (stage i).1 := fun i =>
    hle_of _ _ (by
      rw [hchart, hGker]
      exact hofmono _ _ ((hK_le _).trans (hJ_le i)))
  refine ⟨{
    V := V
    isAffine_V := hV
    φ := φ
    surjective := hs
    etale := he
    I := Ind
    stage := stage
    antitone := ?_
    le_stage := hle
    isFiniteOrderThickening := ?_
    iSup_etaleChartKer := ?_ }⟩
  · intro i j hij
    refine hle_of _ _ ?_
    rw [hchart, hchart]
    exact hofmono _ _ (hK_mono (hJ_mono hij))
  · intro i
    obtain ⟨k, hk⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical ⟨i.1, rfl⟩).2
      ((hJ_le i).trans hnil)
    have hpts : Function.Surjective (pointsMap B S hS (stage i).1.toFunctor (stage i).1.ι) := by
      have hfac : Subfunctor.homOfLe (hle i) ≫ (stage i).1.ι = G.1.ι :=
        Subfunctor.homOfLe_ι _
      have h := hG.2
      rw [← hfac, pointsMap_comp] at h
      exact h.of_comp
    have hKpow : K (J i) ^ (k + 1) = ⊥ := by
      refine le_bot_iff.1 ((Ideal.pow_right_mono (hK_le _) _).trans
        ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans ?_))
      rw [hk, Ideal.zero_eq_bot]
    refine ⟨k, isNthOrderThickening_of_chartKer_pow_eq_bot B S hS hs he (stage i) hpts k ?_⟩
    rw [hchart]
    have h : (Scheme.IdealSheafData.equivOfIsAffine (X := F.obj V)).symm (K (J i) ^ (k + 1)) =
        ⊥ := by
      rw [hKpow, ← Ideal.zero_eq_bot, map_zero, Scheme.IdealSheafData.zero_eq_bot]
    rw [map_pow] at h
    exact h
  · change ⨆ i, chartKer B S hS X (stage i) φ = chartKer B S hS X G φ
    rw [hGker]
    refine Scheme.IdealSheafData.ext_of_isAffine ?_
    rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    simp only [hchart, htop]
    refine le_antisymm (iSup_le fun i => (hK_le _).trans (hJ_le i)) fun n hn => ?_
    have h1 : (F.map s).appTop.hom n ∈ N.map (F.map t).appTop.hom :=
      hkey ▸ Ideal.mem_map_of_mem _ hn
    have hNsup : N = ⨆ i : Ind, J i := by
      refine le_antisymm (fun x hx => ?_) (iSup_le hJ_le)
      have hx' : (↑({x} : Finset Γ(F.obj V, ⊤)) : Set Γ(F.obj V, ⊤)) ⊆ N := by
        simpa using hx
      exact Submodule.mem_iSup_of_mem (p := J) (⟨{x}, hx'⟩ : Ind)
        (Ideal.subset_span (by simp))
    rw [hNsup, Ideal.map_iSup] at h1
    have hdir : Directed (· ≤ ·) fun i : Ind => (J i).map (F.map t).appTop.hom :=
      Monotone.directed_le fun i j h => Ideal.map_mono (hJ_mono h)
    obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 h1
    exact Submodule.mem_iSup_of_mem i (Ideal.mem_comap.2 hi)

end Space

end AlgebraicGeometry

end
