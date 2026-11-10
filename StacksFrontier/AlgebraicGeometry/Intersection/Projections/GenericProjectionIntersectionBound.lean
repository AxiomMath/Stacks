module

public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.ConePoints
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersectionOfCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GenericProjectionIntersection
import all StacksFrontier.AlgebraicGeometry.Intersection.Projections.GenericProjectionIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemma
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericImageFibre

/-!
# The dimension bound for a general projection cone

For closed subsets `Y` and `Z` of `𝐏(V)` whose union is not all of `𝐏(V)`, and for every closed
point `p` of a nonempty Zariski open subset of `𝐏(V)`, the intersection `Y ∩ r_p^{-1}(r_p(Z))`
is `(Y ∩ Z) ∪ E` with `E ⊆ Y` closed and `dim E ≤ dim Y + dim Z + 1 - n`, where `dim V = n + 1`.
The cone `r_p^{-1}(r_p(Z))` is `AlgebraicGeometry.ProjectiveSpaceOfModule.projectionCone` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.GenericProjectionIntersection`, which
proves the decomposition with the bound only in the range `n ≤ dim Z + 1`; here the bound holds
in every range.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq_of_isClosed`:
  the decomposition `Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E` with `E ⊆ Y` closed, together with the
  dimension bound on `E`, for every closed point `p` of a nonempty open subset of `𝐏(V)`.

## Implementation notes

The open of the statement is the complement of `Y ∪ Z` cut down by the open on which the fibres
of the incidence variety are small; the first factor is the open the source works over, and it
is nonempty exactly because `Y ∪ Z` is not all of `𝐏(V)`. That hypothesis is left implicit by
the source, which needs it: for `Y = Z = 𝐏(V)` the asserted identity fails for every `p`, since
the left-hand side misses `p` while `Y ∩ Z` contains it. It is slightly stronger than strictly
necessary — for `Y = 𝐏(V)` and `Z = ∅` the conclusion holds with `E = ∅` — but it is what the
source's choice of `U` requires. The two opens are intersected and the result is nonempty because
the generic point of `𝐏(V)` lies in every nonempty open.

Dimensions take values in `WithBot ℕ∞`, which has no subtraction, so the bound
`dim E ≤ dim Y + dim Z + 1 - n` is stated additively as `dim E + n ≤ dim Y + dim Z + 1`.

The subset `E` produced here is the **closure of `(Y ∩ r_p^{-1}(r_p(Z))) ∖ Z`**. With that
choice the asserted identity is free: `Y ∩ r_p^{-1}(r_p(Z))` is closed, because the image of the
closed `Z` under the projection is closed, the projection being proper on the complement of `p`;
so the closure of the part away from `Z` is inside it, and every point of it is either in `Z` or
in that part. All the content is therefore in the dimension bound, and that is where the
incidence variety enters.

The bound runs as follows, with `T` the incidence variety
`{(y, z, q) : y ∈ Y ∖ Z, z ∈ Z, q ∈ yz}` of
`AlgebraicGeometry.ProjectiveSpaceOfModule.incidenceVariety` taken over the DISTINCT-PAIRS base
`AlgebraicGeometry.ProjectiveSpaceOfModule.prodOfClosedOffSndToProdTwo` of
`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Basic`. The base has to be the
distinct-pairs locus and not all of `Y × Z`: over a pair whose two points coincide every
determinant section vanishes, so the fibre is a whole copy of `𝐏(V)` rather than a line, which is
`range_diagThree_subset_collinearLocus` of
`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Diagonal`. The source's `T` is irreducible;
this one is not known to be, and the argument is arranged so that it need not be.

* `dim T ≤ dim Y + dim Z + 1` is
  `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_incidenceVariety_le`. The
  projection `T ⟶ (Y ∖ Z) × Z` has relative dimension at most one at every point — that is
  `AlgebraicGeometry.ProjectiveSpaceOfModule.relativeDimensionLE_incidenceVarietyToBase`, resting
  on the chart-to-fibre passage
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pointSubmodule_inf_le_pointSubmodule_of_collinear`
  of `StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.FibreLine` — and the base has
  dimension at most `dim Y + dim Z`, which is Tag 0B2M.
* The fibre of `T ⟶ 𝐏(V)` over a general point is
  `AlgebraicGeometry.exists_nonempty_open_topologicalKrullDim_closure_image_fiber_le` of
  `StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericImageFibre`: the upper half of
  Tag 05F7 with the irreducibility of the *source* removed, by decomposing `T` into its finitely
  many irreducible closed pieces. A piece dominating `𝐏(V)` has generic fibre of dimension
  `dim C - n` by Tag 0B2L, so Tag 05F7 applies to it; a piece that does not dominate has empty
  fibre off the closure of its image. That lemma also carries the bound to the closure of the
  image of the fibre under the projection `T ⟶ 𝐏(V)` onto the `Y`-coordinate, which is where `E`
  lives.
* The closed points of `(Y ∩ r_p^{-1}(r_p(Z))) ∖ Z` lie in that image, which is
  `StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.ConePoints`: such a point is collinear
  with `p` and a *closed* point of `Z`, and a collinear triple of closed points is a point of
  `T`. That the triple is a point of the collinearity locus is the converse of the collinearity
  dictionary,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_collinearLocus_of_isClosed` of
  `StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.ConverseCollinear`, and it is the one
  place where the chart coordinate has to be known `k`-LINEAR rather than merely to vanish where
  its numerator is a degree-one equation: the three chart functionals of three collinear points
  kill a common corank-two subspace, hence are linearly dependent, hence every determinant
  vanishes. That linearity is
  `AlgebraicGeometry.ProjectiveSpaceOfModule.chartResidue_chartRatio_smul` of
  `StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.ChartLinear`.
* Only the closed points have to be seen in the image, because `𝐏(V)` is a Jacobson space and
  `(Y ∩ r_p^{-1}(r_p(Z))) ∖ Z` is locally closed, so its closure is the closure of its closed
  points.
* The dimension of a line *is* computed, in
  `StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceDimension`:
  `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_linearSubspace` identifies
  `linearSubspace k V W` with `𝐏(V ⧸ W)` — it is the image of the closed immersion induced by
  `V ⟶ V ⧸ W` — so its dimension is `finrank (V ⧸ W) - 1`, and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_linearSubspace_eq_one` is the
  line.

The final step is available: `Stacks.Intersection.ProjectionFormula.topologicalKrullDim_image_le`
bounds the dimension of a closed subset of the image of a closed subset of a variety; the form
used here is `AlgebraicGeometry.topologicalKrullDim_closure_image_le`, which asks only that the
source have a Noetherian space and not that it be a variety.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **Stacks Project, Tag 0B1R.** For closed subsets `Y` and `Z` of `𝐏(V)` whose union is not
all of `𝐏(V)`, there is a nonempty Zariski open `U` such that for every closed point `p ∈ U` the
intersection `Y ∩ r_p^{-1}(r_p(Z))` is `(Y ∩ Z) ∪ E` with `E ⊆ Y` closed and
`dim E ≤ dim Y + dim Z + 1 - n`, where `dim V = n + 1`.

The decomposition, the closedness of `E` and the dimension bound are all proved for arbitrary
closed `Y` and `Z` rather than only irreducible ones; see the implementation notes for the
incidence-variety argument behind the bound. -/
@[stacks 0B1R "the decomposition Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E with E ⊆ Y closed and the \
dimension bound dim E ≤ dim Y + dim Z + 1 - n, for every closed point p of a nonempty Zariski \
open subset of 𝐏(V); also carrying the hypothesis Y ∪ Z ≠ 𝐏(V), which the source leaves implicit \
and without which the asserted identity fails, the left-hand side missing p while Y ∩ Z contains \
it"]
public theorem exists_isOpen_inter_projectionCone_eq_of_isClosed [IsAlgClosed k] [Module.Finite k V]
    {n : ℕ} (hn : Module.finrank k V = n + 1)
    {Y Z : Set (projectiveSpaceOfModule k V)} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hYZ : Y ∪ Z ≠ Set.univ) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ E : Set (projectiveSpaceOfModule k V), IsClosed E ∧ E ⊆ Y ∧
          topologicalKrullDim ↥E + (n : WithBot ℕ∞) ≤
            topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 ∧
          Y ∩ projectionCone k V p Z = (Y ∩ Z) ∪ E := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by rw [hn]; omega)
  have : FiniteDimensional k V := inferInstance
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
    have := isProper_projectiveSpaceOfModuleToSpec k V
    infer_instance
  have : IrreducibleSpace (projectiveSpaceOfModule k V) :=
    irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k V hn
  have : JacobsonSpace (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn
  -- the degenerate conclusion, with `E` empty
  have htriv : ∀ p : projectiveSpaceOfModule k V, Y ∩ Z = ∅ →
      Y ∩ projectionCone k V p Z = ∅ →
      ∃ E : Set (projectiveSpaceOfModule k V), IsClosed E ∧ E ⊆ Y ∧
        topologicalKrullDim ↥E + (n : WithBot ℕ∞) ≤
          topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 ∧
        Y ∩ projectionCone k V p Z = (Y ∩ Z) ∪ E := by
    intro p hYZ0 hcone0
    refine ⟨∅, isClosed_empty, Set.empty_subset _, ?_, ?_⟩
    · rw [(topologicalKrullDim_eq_bot_iff_isEmpty
        (↥(∅ : Set (projectiveSpaceOfModule k V)))).mpr inferInstance]
      simp
    · rw [hcone0, hYZ0]
      simp
  rcases Set.eq_empty_or_nonempty Y with hYempty | hYne
  · refine ⟨(Y ∪ Z)ᶜ, (hY.union hZ).isOpen_compl, Set.nonempty_compl.mpr hYZ, fun p _ _ => ?_⟩
    exact htriv p (by rw [hYempty]; simp) (by rw [hYempty]; simp)
  rcases Set.eq_empty_or_nonempty Z with hZempty | hZne
  · refine ⟨(Y ∪ Z)ᶜ, (hY.union hZ).isOpen_compl, Set.nonempty_compl.mpr hYZ, fun p _ _ => ?_⟩
    refine htriv p (by rw [hZempty]; simp) ?_
    rw [hZempty, projectionCone]
    simp
  -- the dimensions of `Y` and `Z` as natural numbers
  have hdimeq : ∀ S : Set (projectiveSpaceOfModule k V), S.Nonempty →
      topologicalKrullDim ↥S =
        ((((topologicalKrullDim ↥S).unbotD 0).toNat : ℕ) : WithBot ℕ∞) := fun S hS => by
    have hle : topologicalKrullDim ↥S ≤ (n : WithBot ℕ∞) :=
      le_trans (topologicalKrullDim_subspace_le _ S) (le_of_eq hdimP)
    refine eq_natCast_unbotD_toNat ?_ fun hh => natCast_ne_top_withBot n (top_le_iff.mp (hh ▸ hle))
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    obtain ⟨y, hy⟩ := hS
    exact fun hemp => hemp.false ⟨y, hy⟩
  have hYeq := hdimeq Y hYne
  have hZeq := hdimeq Z hZne
  set m : ℕ := ((topologicalKrullDim ↥Y).unbotD 0).toNat +
    ((topologicalKrullDim ↥Z).unbotD 0).toNat + 1 with hm
  have hmcast : ((m : ℕ) : WithBot ℕ∞) =
      topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 := by
    rw [hYeq, hZeq, hm]
    push_cast
    rfl
  -- the incidence variety over the distinct pairs, and its two morphisms to `𝐏(V)`
  set f := prodOfClosedOffSndToProdTwo k V Y Z hY hZ with hf
  have : LocallyOfFiniteType f := locallyOfFiniteType_prodOfClosedOffSndToProdTwo k V Y Z hY hZ
  have : CompactSpace (incidenceVariety k V f) := compactSpace_incidenceVariety k V Y Z hY hZ
  have : IsClosedImmersion (collinearSubschemeι k V) := isClosedImmersion_collinearSubschemeι k V
  have hpr₃ : LocallyOfFiniteType (pr₃ k V) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (prodTwoToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)) inferInstance
  have : LocallyOfFiniteType (collinearProj₃ k V) :=
    inferInstanceAs (LocallyOfFiniteType (collinearSubschemeι k V ≫ pr₃ k V))
  have : LocallyOfFiniteType (incidenceVarietyToCollinear k V f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (collinearProj k V) f).flip
      inferInstance
  set g := incidenceVarietyToProj k V f with hg
  have : LocallyOfFiniteType g :=
    inferInstanceAs (LocallyOfFiniteType (incidenceVarietyToCollinear k V f ≫ collinearProj₃ k V))
  set h : incidenceVariety k V f ⟶ projectiveSpaceOfModule k V :=
    incidenceVarietyToBase k V f ≫ f ≫
      pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V)
    with hh
  set pT : incidenceVariety k V f ⟶ Spec (.of k) := g ≫ projectiveSpaceOfModuleToSpec k V
    with hpT
  have : LocallyOfFiniteType pT := by rw [hpT]; infer_instance
  have hhT : h ≫ projectiveSpaceOfModuleToSpec k V = pT := by
    have hsq := (isPullback_incidenceVariety k V f).w
    have hcond : prFst k V ≫ prodTwoToSpec k V =
        pr₃ k V ≫ projectiveSpaceOfModuleToSpec k V := pullback.condition
    calc h ≫ projectiveSpaceOfModuleToSpec k V
        = (incidenceVarietyToBase k V f ≫ f) ≫ prodTwoToSpec k V := by
          rw [hh, prodTwoToSpec]
          simp only [Category.assoc]
      _ = (incidenceVarietyToCollinear k V f ≫ collinearProj k V) ≫ prodTwoToSpec k V := by
          rw [hsq]
      _ = incidenceVarietyToCollinear k V f ≫ collinearSubschemeι k V ≫
            (prFst k V ≫ prodTwoToSpec k V) := by
          rw [collinearProj]
          simp only [Category.assoc]
      _ = pT := by
          rw [hcond, hpT, hg, incidenceVarietyToProj, collinearProj₃]
          simp only [Category.assoc]
  have hcsY : topologicalKrullDim (closedSubschemeOf k V Y hY) = topologicalKrullDim ↥Y :=
    topologicalKrullDim_subscheme_vanishingIdeal
      (⟨Y, hY⟩ : Closeds (projectiveSpaceOfModule k V))
  have hcsZ : topologicalKrullDim (closedSubschemeOf k V Z hZ) = topologicalKrullDim ↥Z :=
    topologicalKrullDim_subscheme_vanishingIdeal
      (⟨Z, hZ⟩ : Closeds (projectiveSpaceOfModule k V))
  have hTdim : topologicalKrullDim (incidenceVariety k V f) ≤ ((m : ℕ) : WithBot ℕ∞) := by
    refine le_trans (topologicalKrullDim_incidenceVariety_le k V Y Z hY hZ) ?_
    rw [hcsY, hcsZ, hmcast]
  obtain ⟨U₀, hU₀open, hU₀ne, hU₀dim⟩ :=
    exists_nonempty_open_topologicalKrullDim_closure_image_fiber_le k pT
      (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) g rfl h hhT
      hTdim hdimP
  -- the open set
  refine ⟨(Y ∪ Z)ᶜ ∩ U₀, (hY.union hZ).isOpen_compl.inter hU₀open, ?_, ?_⟩
  · have hgen : ∀ W : Set (projectiveSpaceOfModule k V), IsOpen W → W.Nonempty →
        genericPoint (projectiveSpaceOfModule k V) ∈ W := fun W hW ⟨q, hq⟩ =>
      ((genericPoint_spec _).mem_open_set_iff hW).mpr ⟨q, Set.mem_univ q, hq⟩
    exact ⟨genericPoint (projectiveSpaceOfModule k V),
      hgen _ (hY.union hZ).isOpen_compl (Set.nonempty_compl.mpr hYZ), hgen _ hU₀open hU₀ne⟩
  intro p hp hpc
  obtain ⟨hpYZ, hpU₀⟩ := hp
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at hpYZ
  obtain ⟨hpY, hpZ⟩ := hpYZ
  rcases subsingleton_or_nontrivial ↥(pointSubmodule k V p) with hWs | hWnt
  · -- `p` has no hyperplane, so `𝐏(V)` is the single point `p` and `Y` is empty
    exfalso
    have hbot : pointSubmodule k V p = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      simpa using congrArg Subtype.val
        (Subsingleton.elim (⟨x, hx⟩ : ↥(pointSubmodule k V p)) 0)
    have huniv : (Set.univ : Set (projectiveSpaceOfModule k V)) = {p} := by
      rw [← linearSubspace_pointSubmodule k V p hpc, hbot, linearSubspace_bot]
    obtain ⟨y, hy⟩ := hYne
    have hy1 : y ∈ ({p} : Set (projectiveSpaceOfModule k V)) := by rw [← huniv]; trivial
    exact hpY (Set.mem_singleton_iff.mp hy1 ▸ hy)
  · -- the cone is closed away from `p`
    have hdisj : Disjoint Z (linearSubspace k V (pointSubmodule k V p)) := by
      rw [linearSubspace_pointSubmodule k V p hpc]
      exact Set.disjoint_singleton_right.mpr hpZ
    have hKclosed := isClosed_image_projection k V (pointSubmodule k V p) hZ hdisj
    have hpre : IsClosed ((projection k V (pointSubmodule k V p)).base ⁻¹'
        ((projection k V (pointSubmodule k V p)).base ''
          ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' Z))) :=
      hKclosed.preimage (Scheme.Hom.continuous (projection k V (pointSubmodule k V p)))
    obtain ⟨C, hCclosed, hCeq⟩ :=
      (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.isInducing.isClosed_iff.mp
        hpre
    have hcone : projectionCone k V p Z = C ∩ {p}ᶜ := by
      rw [projectionCone, ← hCeq, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι,
        coe_mapDomain_pointSubmodule k V p hpc]
    have hEeq : Y ∩ projectionCone k V p Z = Y ∩ C := by
      rw [hcone]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, fun hxp => hpY (hxp ▸ hx.1)⟩⟩
    refine ⟨closure ((Y ∩ C) \ Z), isClosed_closure, ?_, ?_, ?_⟩
    · exact closure_minimal (fun x hx => hx.1.1) hY
    · -- the dimension bound
      have hSlc : IsLocallyClosed ((Y ∩ C) \ Z) := by
        rw [Set.sdiff_eq]
        exact (hY.inter hCclosed).isLocallyClosed.inter hZ.isOpen_compl.isLocallyClosed
      have hsub : ((Y ∩ C) \ Z) ∩ closedPoints (projectiveSpaceOfModule k V) ⊆
          h.base '' (g.base ⁻¹' {p}) := by
        rintro x ⟨⟨⟨hxY, hxC⟩, hxZ⟩, hxcp⟩
        have hxc : IsClosed ({x} : Set (projectiveSpaceOfModule k V)) := hxcp
        have hxp : x ≠ p := fun hxp => hpY (hxp ▸ hxY)
        have hxcone : x ∈ projectionCone k V p Z := by
          rw [hcone]
          exact ⟨hxC, hxp⟩
        obtain ⟨x', hx'mem, hx'eq⟩ := hxcone
        obtain ⟨z', hz'Z, hz'proj⟩ := hx'mem
        obtain ⟨z, hzZ, hzc, hle⟩ := exists_isClosed_of_projection_eq k V hpc hxc hxp hWnt hZ
          hpZ hx'eq hz'Z hz'proj
        have hpz : p ≠ z := fun hpz => hpZ (hpz ▸ hzZ)
        have hxz : x ≠ z := fun hxz => hxZ (hxz ▸ hzZ)
        obtain ⟨τ, hτp, hτx⟩ := exists_mem_incidenceVariety k V Y Z hY hZ hxc hzc hpc hxY hxZ
          hzZ (pointSubmodule_inf_le_of_inf_le k V hpc hxc hzc hpz hxz hle)
        refine ⟨τ, hτp, ?_⟩
        have hbase : h.base τ = (pullback.fst (projectiveSpaceOfModuleToSpec k V)
            (projectiveSpaceOfModuleToSpec k V)).base
              (f.base ((incidenceVarietyToBase k V f).base τ)) := rfl
        rw [hbase]
        exact hτx
      have hclos : closure ((Y ∩ C) \ Z) ⊆ closure (h.base '' (g.base ⁻¹' {p})) := by
        rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure hSlc]
        exact closure_mono hsub
      rw [← hmcast]
      exact le_trans (add_le_add (topologicalKrullDim_le_of_subset hclos)
        (le_refl ((n : ℕ) : WithBot ℕ∞))) (hU₀dim p hpU₀ hpc)
    · -- the identity
      rw [hEeq]
      refine Set.Subset.antisymm (fun x hx => ?_) (Set.union_subset ?_ ?_)
      · by_cases hxZ : x ∈ Z
        · exact Or.inl ⟨hx.1, hxZ⟩
        · exact Or.inr (subset_closure ⟨hx, hxZ⟩)
      · rw [← hEeq]
        rintro x ⟨hxY, hxZ⟩
        exact ⟨hxY, subset_projectionCone k V p hpc Z hxZ fun hxp => hpY (hxp ▸ hxY)⟩
      · exact closure_minimal (fun x hx => hx.1) (hY.inter hCclosed)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
