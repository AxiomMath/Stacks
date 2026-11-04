module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealChain
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullbackFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingLocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStrata
public import StacksFrontier.AlgebraicGeometry.Spaces.HomOverIdealUnitLocus

/-!
# Clause (3) of Stacks 0CZ9: the rank-`r` stratum represents local freeness of rank `r`

Let `Y` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `G` be a
quasi-coherent `𝒪_Y`-module of finite type and let `Y ⊇ Z_0 ⊇ Z_1 ⊇ …` be the chain of closed
subspaces cut out by the Fitting ideals of `G`.  With the convention `Z_{-1} = Y`, the rank-`r`
stratum is the locally closed subspace `Y_r = Z_{r-1} \ Z_r`.  Clause (3) of Stacks 0CZ9 says
that `Y_r` represents the functor sending a space over `Y` to a one-point set when the pullback
of `G` to it is locally free of rank `r` and to the empty set otherwise.

The two halves of the stratum are read separately.  Factoring through the open complement
`Y \ Z_r` is clause (2), `AlgebraicGeometry.Space.existsUnique_lift_openComplement_iff_forall_
exists_fin_span`, and the condition it produces — local generation of `f^*G` by `r` sections
around every point — is the statement that the `r`-th Fitting ideal sheaf of `f^*G` is the unit
ideal sheaf.  Factoring through the closed subspace `Z_{r-1}` is the ideal criterion of
Stacks 03MB read on the diagrams of affine étale charts over `f`,
`AlgebraicGeometry.Space.range_le_iff_forall_chartDiagram_definingIdealAt_le`, and the condition
it produces is, through the base change of Fitting ideals (Stacks 0CZ4), the vanishing of the
`(r-1)`-st Fitting ideal sheaf of `f^*G`.  Those are exactly the two conditions which
Stacks 0CZ8, `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_tfae_fittingIdeal`, equates with
local freeness of rank `r`.

## Main results

* `AlgebraicGeometry.Space.fittingIdeal_modulePullback_eq_bot_iff_range_le`: the `k`-th Fitting
  ideal sheaf of `f^*G` vanishes exactly when `f` lands in the `k`-th Fitting closed subspace.
* `AlgebraicGeometry.Space.fittingIdeal_modulePullback_eq_top_iff_forall_exists_fin_span`: the
  `r`-th Fitting ideal sheaf of `f^*G` is the unit ideal sheaf exactly when `f^*G` is generated
  by `r` sections on an affine étale chart around every point.
* `AlgebraicGeometry.Space.existsUnique_lift_fittingRankStratum_iff` is **clause (3) of
  Stacks 0CZ9**, from the tag's own hypotheses.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_fittingRankStratumHom` is
  the **local-freeness claim of Stacks 0CZA**: `G` restricted to the stratum `Y_r` is finite
  locally free of rank `r`.  It is clause (3) read at the inclusion of the stratum.  The tag
  0CZA is registered not here but on the collected statement
  `AlgebraicGeometry.Space.exists_fittingRankStratification_flat_spec` of
  `StacksFrontier/AlgebraicGeometry/Spaces/FittingStratumAssembly.lean`.

## Implementation notes

The vanishing criterion is routed through the inverse-image Fitting ideal sheaf
`AlgebraicGeometry.Space.fittingIdealPullback` rather than through the affine charts of `X`
directly, so that no cofinality argument is needed: the ideal-sheaf form of Stacks 0CZ4,
`AlgebraicGeometry.Space.fittingIdealPullback_eq_fittingIdeal`, is
unconditional on the tag's hypotheses, and `fittingIdealPullback` is by construction the
smallest sheaf of ideals whose sections over the source chart of every affine chart diagram
contain the image of the chartwise Fitting ideal over the target chart.  Its vanishing is
therefore literally a condition on the affine chart diagrams, which is the shape the ideal
criterion delivers.

In the other direction the chartwise Fitting ideal of `f^*G` over the source chart of a diagram
is read through `AlgebraicGeometry.Space.fittingIdealOnChart_modulePullback`, the chartwise form
of Stacks 0CZ4, whose cartesian input across `f` is Descent, Proposition 03DX(2) in the proved
form `AlgebraicGeometry.Space.isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite`.

That the unit locus of the `r`-th Fitting ideal sheaf being everything forces that sheaf to be
the unit ideal sheaf is `AlgebraicGeometry.Space.idealSheaf_obj_eq_top_of_range_subset_
idealUnitLocus`: membership in a sheaf of ideals is local, and the charts carrying the unit
ideal cover a chart all of whose points lie in the unit locus.

Nothing is assumed beyond the tag's own hypotheses on `G`.  The finite presentation clause of
Stacks 0CZ9 is not proved here; its closed-subspace part is
`AlgebraicGeometry.Space.isFinitePresentation_fittingClosedSubspace` in
`StacksFrontier/AlgebraicGeometry/Spaces/FittingClosedSubspaceFinitePresentation.lean`, and the
module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/FittingStratificationFiniteType.lean` records what the
remaining two morphisms of the clause still need.

## References

* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 0CZ8](https://stacks.math.columbia.edu/tag/0CZ8)
* [Stacks Project, Tag 0CZ4](https://stacks.math.columbia.edu/tag/0CZ4)
* [Stacks Project, Tag 0CZ3](https://stacks.math.columbia.edu/tag/0CZ3)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The vanishing clause -/

/-- **The `k`-th Fitting ideal sheaf of `f^*G` vanishes exactly when `f` lands in the `k`-th
Fitting closed subspace.**  Let `G` be a quasi-coherent `𝒪_Y`-module of finite type and let `Z`
be the closed subspace of `Y` cut out by the `k`-th Fitting ideal of `G`.

The ideal criterion of Stacks 03MB, read on the diagrams of affine étale charts over `f`, turns
the right-hand side into the vanishing of the image of the chartwise `k`-th Fitting ideal of `G`
over the target chart of every such diagram; by the base change of Fitting ideals, Stacks 0CZ4,
that is the vanishing of the chartwise `k`-th Fitting ideal of `f^*G` over the source chart, and
the inverse-image Fitting ideal sheaf is by construction generated by exactly those. -/
theorem fittingIdeal_modulePullback_eq_bot_iff_range_le
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hGqc : G.IsQuasicoherentOnSite)
    (hGft : SheafOfModules.IsFiniteTypeOnSite G) (Z : ClosedSubspaces B S hS Y.1) (k : ℕ)
    (hZ : definingIdealSheaf B S hS Y Z = fittingIdeal B S hS Y.1 Y.2 G k) (f : X ⟶ Y) :
    fittingIdeal B S hS X.1 X.2 ((modulePullback B S hS f).obj G) k = ⊥ ↔
      Subfunctor.range f.hom ≤ Z.1 := by
  have hcartG : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 G hGqc
  have hfinG := module_finite_sections_of_isFiniteTypeOnSite G hGqc hGft
  -- the defining ideal of `Z` at an affine chart of `Y` is the chartwise Fitting ideal there
  have hZchart : ∀ V : SmallEtale B S hS Y.1,
      ∀ hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj V),
      definingIdealAt B S hS Y Z (op V) =
        @fittingIdealOnChart B S hS Y.1 Y.2 G k V (hfinG V hV) := by
    intro V hV
    rw [show definingIdealAt B S hS Y Z (op V) =
      (definingIdealSheaf B S hS Y Z).toSubmodule.obj (op V) from rfl, hZ]
    exact fittingIdeal_obj_eq_fittingIdealOnChart G hcartG hfinG k hV
  rw [range_le_iff_forall_chartDiagram_definingIdealAt_le]
  constructor
  · intro hbot d hdU hdV b hb
    have := hfinG d.V hdV
    obtain ⟨e⟩ := isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite B S hS f G hGqc
      d hdU hdV
    have := module_finite_sections_modulePullback (f := f) (G := G) (d := d) e
    rw [hZchart d.V hdV] at hb
    have hb' : chartDiagramRestrict B S hS f d b ∈
        fittingIdealOnChart B S hS X.1 X.2 ((modulePullback B S hS f).obj G) k d.U := by
      rw [fittingIdealOnChart_modulePullback k e]
      exact Ideal.mem_map_of_mem (chartDiagramRestrict B S hS f d) hb
    have hmem := mem_fittingIdeal_of_mem_fittingIdealOnChart
      ((modulePullback B S hS f).obj G) k d.U hdU _ hb'
    rw [hbot] at hmem
    exact (SheafOfModules.Submodule.bot_obj _ (op d.U)).le hmem
  · intro hker
    rw [← fittingIdealPullback_eq_fittingIdeal (f := f) hGqc
      (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite G hGft) k]
    refine le_antisymm (fittingIdealPullback_le k fun d hdU hdV hfin b hb ↦ ?_) bot_le
    have hle : @fittingIdealOnChart B S hS Y.1 Y.2 G k d.V hfin ≤
        RingHom.ker (chartDiagramRestrict B S hS f d) :=
      (hZchart d.V hdV).ge.trans (hker d hdU hdV)
    rw [(Ideal.map_eq_bot_iff_le_ker _).2 hle] at hb
    obtain rfl : b = 0 := by simpa using hb
    exact _root_.Submodule.zero_mem _

/-! ### The unit clause -/

/-- **The `r`-th Fitting ideal sheaf of `f^*G` is the unit ideal sheaf exactly when `f^*G` is
generated by `r` sections around every point.**  One direction is that the unit ideal sheaf has
all of `X` as its unit locus, the other that a sheaf of ideals whose unit locus is everything is
the unit ideal sheaf. -/
theorem fittingIdeal_modulePullback_eq_top_iff_forall_exists_fin_span
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hGqc : G.IsQuasicoherentOnSite)
    (hGft : SheafOfModules.IsFiniteTypeOnSite G) (r : ℕ) (f : X ⟶ Y) :
    fittingIdeal B S hS X.1 X.2 ((modulePullback B S hS f).obj G) r = ⊤ ↔
      ∀ x : points B S hS X.1, ∃ (U : SmallEtale B S hS X.1)
        (s : Fin r → ((modulePullback B S hS f).obj G).val.obj (op U)),
        IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U) ∧
          Submodule.span (chartRing B S hS X.1 X.2 U) (Set.range s) = ⊤ ∧
          x ∈ Set.range (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom) := by
  have hpbqc : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hGqc
  have hcartP : IsCartesianOnAffineCharts ((modulePullback B S hS f).obj G) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _ hpbqc
  have hfinP := module_finite_sections_of_isFiniteTypeOnSite _ hpbqc
    (isFiniteTypeOnSite_modulePullback B S hS f G hGft)
  have hiff : (∀ x : points B S hS X.1, x ∈ idealUnitLocus B S hS X
      (fittingIdeal B S hS X.1 X.2 ((modulePullback B S hS f).obj G) r)) ↔ _ :=
    forall_congr' fun x ↦ mem_idealUnitLocus_fittingIdeal_iff B S hS X _ hcartP hfinP r x
  refine Iff.trans ?_ hiff
  constructor
  · intro htop x
    have htop' : fittingIdeal B S hS X.1 X.2 ((modulePullback B S hS f).obj G) r =
        (⊤ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) := htop
    rw [htop', idealUnitLocus_top]
    exact Set.mem_univ x
  · intro hall
    refine le_antisymm le_top (SheafOfModules.Submodule.le_iff.mpr
      (PresheafOfModules.Submodule.le_iff.mpr fun W x _ ↦ ?_))
    have hW : (fittingIdeal B S hS X.1 X.2
        ((modulePullback B S hS f).obj G) r).toSubmodule.obj W = ⊤ :=
      idealSheaf_obj_eq_top_of_range_subset_idealUnitLocus B S hS X
        (fittingIdeal B S hS X.1 X.2 ((modulePullback B S hS f).obj G) r) W.unop
        fun z _ ↦ hall z
    rw [hW]
    exact Submodule.mem_top

/-! ### Clause (3) of Stacks 0CZ9 -/

/-- **Clause (3) of Stacks 0CZ9, from the tag's own hypotheses.**  Let `Y` be an algebraic space
over `S`, let `G` be a quasi-coherent `𝒪_Y`-module of finite type and let `Y ⊇ Z_0 ⊇ Z_1 ⊇ …` be
the chain of closed subspaces cut out by the Fitting ideals of `G`.  Then the locally closed
subspace `Y_r = Z_{r-1} \ Z_r` represents the functor sending a space over `Y` to a one-point
set when the pullback of `G` to it is finite locally free of rank `r` and to the empty set
otherwise: a morphism `f : X ⟶ Y` factors through `Y_r`, necessarily uniquely, exactly when
`f^*G` is finite locally free of rank `r`.

The test object is an arbitrary algebraic space over `S`, which contains the schemes over `Y` of
the tag's `(\Sch/Y)`.  Local freeness of rank `r` is the rank clause of Stacks 0409,
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`.

Nothing beyond quasi-coherence and finite type of `G` is asked for: the two halves of the
stratum are matched with the two Fitting conditions of Stacks 0CZ8 by
`AlgebraicGeometry.Space.fittingIdeal_modulePullback_eq_bot_iff_range_le` and
`AlgebraicGeometry.Space.fittingIdeal_modulePullback_eq_top_iff_forall_exists_fin_span`, and
Stacks 0CZ8 is applied to `f^*G`, whose quasi-coherence is Stacks 03GA. -/
theorem existsUnique_lift_fittingRankStratum_iff
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hGqc : G.IsQuasicoherentOnSite)
    (hGft : SheafOfModules.IsFiniteTypeOnSite G) (Z : ℕ → ClosedSubspaces B S hS Y.1)
    (hZ : ∀ r, definingIdealSheaf B S hS Y (Z r) = fittingIdeal B S hS Y.1 Y.2 G r)
    (r : ℕ) (f : X ⟶ Y) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
        ((modulePullback B S hS f).obj G) r ↔
      ∃! g : X.1 ⟶ (fittingRankStratum B S hS Y Z r).toFunctor,
        g ≫ (fittingRankStratum B S hS Y Z r).ι = f.hom := by
  have hpbqc : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hGqc
  have htfae := isFiniteLocallyFreeOfRank_tfae_fittingIdeal B S hS X.1 X.2
    ((modulePullback B S hS f).obj G) hpbqc r
  -- the open half: generation by `r` sections, hence the unit Fitting ideal sheaf
  have hopen : Subfunctor.range f.hom ≤ openComplement B S hS (Z r).1 ↔
      fittingIdeal B S hS X.1 X.2 ((modulePullback B S hS f).obj G) r = ⊤ := by
    rw [← existsUnique_lift_iff_range_le,
      ← existsUnique_lift_openComplement_iff_forall_exists_fin_span B S hS G hGqc hGft Z hZ r f,
      fittingIdeal_modulePullback_eq_top_iff_forall_exists_fin_span B S hS G hGqc hGft r f]
  -- the closed half: the vanishing of the previous Fitting ideal sheaf
  have hclosed : Subfunctor.range f.hom ≤ closedChainPred B S hS Y Z r ↔
      (r = 0 ∨ fittingIdeal B S hS X.1 X.2
        ((modulePullback B S hS f).obj G) (r - 1) = ⊥) := by
    cases r with
    | zero => simp [closedChainPred_zero]
    | succ k =>
      rw [closedChainPred_succ]
      simp only [Nat.add_one_sub_one, Nat.succ_ne_zero, false_or]
      exact (fittingIdeal_modulePullback_eq_bot_iff_range_le B S hS G hGqc hGft (Z k) k
        (hZ k) f).symm
  refine (htfae.out 1 2).trans ?_
  rw [← hclosed, ← hopen, ← le_inf_iff]
  exact (existsUnique_lift_iff_range_le B S hS
    (fittingRankStratum B S hS Y Z r) f.hom).symm

/-! ### The restriction of `G` to a stratum -/

/-- **The local-freeness claim of Stacks 0CZA.**  The pullback of `G` to the rank-`r` stratum
`Y_r = Z_{r-1} \ Z_r` is finite locally free of rank `r`.

This is clause (3) read at the inclusion of the stratum itself, which factors through the
stratum by the identity.  The tag is registered on the collected statement
`AlgebraicGeometry.Space.exists_fittingRankStratification_spec`, which consumes this. -/
theorem isFiniteLocallyFreeOfRank_modulePullback_fittingRankStratumHom
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hGqc : G.IsQuasicoherentOnSite)
    (hGft : SheafOfModules.IsFiniteTypeOnSite G) (Z : ℕ → ClosedSubspaces B S hS Y.1)
    (hZ : ∀ r, definingIdealSheaf B S hS Y (Z r) = fittingIdeal B S hS Y.1 Y.2 G r) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite B S hS (fittingRankStratumSpace B S hS Y Z r).1
          (fittingRankStratumSpace B S hS Y Z r).2)
        ((modulePullback B S hS (fittingRankStratumHom B S hS Y Z r)).obj G) r :=
  (existsUnique_lift_fittingRankStratum_iff B S hS G hGqc hGft Z hZ r
    (fittingRankStratumHom B S hS Y Z r)).2 ⟨𝟙 _, Category.id_comp _, fun _ hy ↦
      (cancel_mono (fittingRankStratum B S hS Y Z r).ι).1 (hy.trans (Category.id_comp _).symm)⟩

end AlgebraicGeometry.Space

end
