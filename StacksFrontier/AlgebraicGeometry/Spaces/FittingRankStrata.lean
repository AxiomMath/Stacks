module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The Fitting rank strata of an algebraic space and their disjoint union

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`X ⊇ Z_0 ⊇ Z_1 ⊇ …` be the decreasing chain of closed subspaces cut out by the Fitting ideals
of an `𝒪_X`-module, as constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/FittingClosedSubspaces.lean`.  With the convention
`Z_{-1} = X`, the rank-`r` stratum is the locally closed subspace

`X_r = Z_{r-1} \ Z_r`.

This file constructs those strata, shows that each is a locally closed subspace of `X` and that
distinct strata are disjoint, and forms their disjoint union `X' = ∐_{r ≥ 0} X_r` as an algebraic
space over `S` with its structural morphism to `X`.

## Main definitions

* `AlgebraicGeometry.Space.closedChainPred`: the predecessor `Z_{r-1}` in the chain, equal to the
  whole space for `r = 0`.
* `AlgebraicGeometry.Space.fittingRankStratum`: the stratum `X_r = Z_{r-1} \ Z_r`, as a subfunctor
  of `X`.
* `AlgebraicGeometry.Space.fittingRankStratumSpace`: the same stratum, as an algebraic space
  over `S`.
* `AlgebraicGeometry.Space.fittingRankStratification` and
  `AlgebraicGeometry.Space.fittingRankStratificationHom`: the disjoint union `X' = ∐_{r ≥ 0} X_r`
  and its structural morphism to `X`.

## Main results

* `AlgebraicGeometry.Space.isLocallyClosedSubspace_inf_openComplement`: the part of a closed
  subspace lying outside a second closed subspace is a locally closed subspace.
* `AlgebraicGeometry.Space.isLocallyClosedSubspace_fittingRankStratum`: each stratum is a locally
  closed subspace of `X`.
* `AlgebraicGeometry.Space.fittingRankStratum_inf_le_sheafify_bot`: distinct strata of a
  decreasing chain are disjoint.
* `AlgebraicGeometry.Space.existsUnique_stratum_index`: every point of the ambient space lies in
  exactly one stratum of a chain whose point sets have empty intersection.
* `AlgebraicGeometry.Space.isLocallyClosedSubspace_and_disjoint_fittingRankStratum`: the
  Fitting rank strata are pairwise disjoint locally closed subspaces of `X`.
* `AlgebraicGeometry.Space.existsUnique_fittingRankStratum_index`: every point of `X` lies in
  exactly one Fitting rank stratum.
* `AlgebraicGeometry.Space.isAlgebraicSpace_fittingRankStratification`: the disjoint union
  `X' = ∐_{r ≥ 0} X_r` is an algebraic space over `S` whose structural morphism restricts on the
  `r`-th summand to the inclusion of `X_r`.

These three are clauses of Stacks 0CZA, and each carries a clause-qualified registration; the
whole tag is collected in `AlgebraicGeometry.Space.exists_fittingRankStratification_flat_spec`
of `StacksFrontier/AlgebraicGeometry/Spaces/FittingStratumAssembly.lean`.

## Implementation notes

The stratum is the meet `Z_{r-1} ⊓ (X \ Z_r)` of a closed and an open subspace of `X`, where
`X \ Z_r` is the open complement `AlgebraicGeometry.Space.openComplement` of
`StacksFrontier/AlgebraicGeometry/Spaces/OpenComplement.lean`.  That this meet is a locally closed
subspace is proved by exhibiting it as the range of a closed immersion followed by an open
immersion: the inverse image of `Z_{r-1}` in the open subspace `X \ Z_r` is a closed subspace
of `X \ Z_r`, and the meet is the range of its inclusion into `X`.  Part (6) of Stacks 02YU asks
exactly for the algebraicity of the range and for its inclusion to be an immersion, which is
Stacks 02YV part (3) applied to that factorisation.

Disjointness is stated as containment in the sheafification of the bottom subfunctor, the empty
algebraic subspace, as clause (1) of Stacks 0CZ9 is stated in
`AlgebraicGeometry.Space.iInf_fittingClosedSubspace_eq_sheafify_bot`.  For `r < s` the stratum
`X_s` lies in `Z_{s-1} ⊆ Z_r` while `X_r` lies in `X \ Z_r`, so the meet has no points at all,
and part (1) of Stacks 03BZ turns that into containment in an open subspace with no points.

The disjoint union is the coproduct in the category of algebraic spaces over `S`, which exists
for a countable index type by Stacks 02WQ in the form
`AlgebraicGeometry.Space.hasColimitsOfShape_discrete_algebraicSpaces`; its algebraicity is
therefore part of the construction rather than a separate argument.

The chain is taken as input, as it is in
`AlgebraicGeometry.Space.iInf_fittingClosedSubspace_eq_sheafify_bot`: the closed subspaces cut
out by the Fitting ideals are produced by the existential
`AlgebraicGeometry.Space.exists_fittingClosedSubspaces`, which is not a construction.  The
statements about an arbitrary decreasing chain are therefore the general ones, and the Fitting
ideals enter only through the hypothesis that they are the defining ideal sheaves of the chain.
The hypothesis `hfin` of
`AlgebraicGeometry.Space.existsUnique_fittingRankStratum_index` is not a debt: it follows from
quasi-coherence and finite type by
`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`.  The statements of this
file are collected with it discharged, and with the chain produced from the hypotheses
Stacks 0CZA itself makes, in
`AlgebraicGeometry.Space.exists_fittingRankStratification_of_isFinitePresentationOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/FittingStratificationFiniteType.lean`.

That the module is finite locally free of rank `r` on `X_r` is not proved here but in
`StacksFrontier/AlgebraicGeometry/Spaces/FittingRankStratumRepresentable.lean`, as
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_fittingRankStratumHom`, on the
tag's own hypotheses: it is clause (3) of Stacks 0CZ9 read at the inclusion of the stratum
itself.  The ideal-theoretic universal property of a closed subspace is Stacks 03MB, proved in
`StacksFrontier/AlgebraicGeometry/Spaces/FactorThroughClosedSubspace.lean`,
which asks nothing of the
source, and what clause (3) needs is its chart-diagram reading,
`AlgebraicGeometry.Space.range_le_iff_forall_chartDiagram_definingIdealAt_le`.

One assertion of Stacks 0CZA remains unproved: that `X'` represents the functor of flatness of
`G_T`.  It needs, beyond clause (3), a flatness predicate for a module on the small étale site
of an arbitrary test space and the implication that a module of finite presentation is finite
locally free there as soon as it is flat; the commutative algebra for the latter is
`Module.isFiniteLocallyFree_iff`, but the stalk criterion identifying tensor-exactness with
pointwise flatness, Stacks 05NE, is available only for the topology of opens of a topological
space, so neither that implication nor its converse is in the tree.

That `X' → X` is of finite presentation *is* now proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/FittingStratificationFinitePresentation.lean` as
`AlgebraicGeometry.Space.isFinitePresentation_fittingRankStratificationHom`.  It is not the same
statement as finite presentation of the strata,
`AlgebraicGeometry.Space.isFinitePresentation_ι_fittingRankStratum`: a coproduct of infinitely
many morphisms of finite presentation need not be quasi-compact, and what is additionally used
is that over an affine test object all but finitely many strata are empty.  Neither claim
rests on the chart comparison `hchart` of
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart`
(Stacks 084Q).

## References

* [Stacks Project, Tag 0CZA](https://stacks.math.columbia.edu/tag/0CZA)
* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YV](https://stacks.math.columbia.edu/tag/02YV)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The part of a closed subspace outside another closed subspace -/

/-- The meet of two subfunctors is the range of the inclusion into the ambient presheaf of the
inverse image of the second in the first. -/
theorem inf_eq_range_preimage_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U V : Subfunctor F) :
    U ⊓ V = Subfunctor.range ((V.preimage U.ι).ι ≫ U.ι) := by
  ext T x
  constructor
  · exact fun hx ↦ ⟨⟨⟨x, hx.1⟩, hx.2⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.1.2, y.2⟩

/-- The range of an immersion with algebraic source is a locally closed subspace: the morphism
to its range is an isomorphism because the morphism is a monomorphism. -/
theorem isLocallyClosedSubspace_range {F Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ F)
    [Mono f] (hY : IsAlgebraicSpace B S hS Y) (hf : IsImmersion B S hS f) :
    IsLocallyClosedSubspace B S hS (Subfunctor.range f) := by
  have hι : inv (Subfunctor.toRange f) ≫ f = (Subfunctor.range f).ι :=
    (IsIso.inv_comp_eq (Subfunctor.toRange f)).2 (Subfunctor.toRange_ι f).symm
  refine ⟨isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange f)) hY, ?_⟩
  have hpre := MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    (inv (Subfunctor.toRange f)) f hf
  rwa [hι] at hpre

/-- **The part of a closed subspace lying outside a second closed subspace is a locally closed
subspace.**

The inverse image of `W` in the open complement of `T` is a closed subspace of that complement,
so the meet `W ⊓ (X \ T)` is the range of a closed immersion followed by an open immersion, and
a composite of immersions is an immersion. -/
theorem isLocallyClosedSubspace_inf_openComplement (W T : Subfunctor X.1)
    (hW : IsClosedSubspace B S hS W) (hT : IsClosedSubspace B S hS T) :
    IsLocallyClosedSubspace B S hS (W ⊓ openComplement B S hS T) := by
  have hU : IsOpenSubspace B S hS (openComplement B S hS T) :=
    isOpenSubspace_openComplement B S hS X.2 T hT
  have hpre : IsClosedSubspace B S hS (W.preimage (openComplement B S hS T).ι) :=
    isClosedSubspace_preimage B S hS (openComplement B S hS T).ι W X.2 hU.1 hW
  rw [inf_comm, inf_eq_range_preimage_ι B S hS (openComplement B S hS T) W]
  exact isLocallyClosedSubspace_range B S hS _ hpre.1
    (isImmersion_comp B S hS _ _ (isImmersion_of_isClosedImmersion B S hS hpre.2)
      (isImmersion_of_isOpenImmersion B S hS hU.2))

/-- The top subfunctor of an algebraic space is a closed subspace of it: its inclusion is an
isomorphism. -/
theorem isClosedSubspace_top_subfunctor {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    IsClosedSubspace B S hS (⊤ : Subfunctor F) :=
  ⟨hF.of_iso (asIso (Subfunctor.ι (⊤ : Subfunctor F))).symm,
    isClosedImmersion_of_isIso B S hS _⟩

/-! ### The strata of a decreasing chain of closed subspaces -/

/-- The predecessor `Z_{r-1}` of the `r`-th member of a chain `X ⊇ Z_0 ⊇ Z_1 ⊇ …` of closed
subspaces of an algebraic space, with the convention `Z_{-1} = X` of Stacks 0CZ9. -/
def closedChainPred (Z : ℕ → ClosedSubspaces B S hS X.1) : ℕ → Subfunctor X.1
  | 0 => ⊤
  | r + 1 => (Z r).1

/-- The predecessor of the zeroth member of a chain of closed subspaces is the whole space. -/
@[simp]
theorem closedChainPred_zero (Z : ℕ → ClosedSubspaces B S hS X.1) :
    closedChainPred B S hS X Z 0 = ⊤ := rfl

/-- The predecessor of the `(r + 1)`-st member of a chain of closed subspaces is `Z r`. -/
@[simp]
theorem closedChainPred_succ (Z : ℕ → ClosedSubspaces B S hS X.1) (r : ℕ) :
    closedChainPred B S hS X Z (r + 1) = (Z r).1 := rfl

/-- The predecessor of a member of a chain of closed subspaces is a closed subspace. -/
theorem isClosedSubspace_closedChainPred (Z : ℕ → ClosedSubspaces B S hS X.1) (r : ℕ) :
    IsClosedSubspace B S hS (closedChainPred B S hS X Z r) := by
  cases r with
  | zero => exact isClosedSubspace_top_subfunctor B S hS X.2
  | succ k => exact (Z k).2

/-- **The rank-`r` stratum `X_r = Z_{r-1} \ Z_r`** of a chain `X ⊇ Z_0 ⊇ Z_1 ⊇ …` of closed
subspaces of an algebraic space, as a subfunctor of the ambient space: the part of the
predecessor `Z_{r-1}` lying in the open complement of `Z_r`. -/
def fittingRankStratum (Z : ℕ → ClosedSubspaces B S hS X.1) (r : ℕ) : Subfunctor X.1 :=
  closedChainPred B S hS X Z r ⊓ openComplement B S hS (Z r).1

/-- The stratum `X_0` of a chain of closed subspaces is the open complement of `Z 0`. -/
@[simp]
theorem fittingRankStratum_zero (Z : ℕ → ClosedSubspaces B S hS X.1) :
    fittingRankStratum B S hS X Z 0 = openComplement B S hS (Z 0).1 := by
  rw [fittingRankStratum, closedChainPred_zero, top_inf_eq]

/-- The stratum `X_{r+1}` of a chain of closed subspaces is the part of `Z r` lying in the open
complement of `Z (r + 1)`. -/
@[simp]
theorem fittingRankStratum_succ (Z : ℕ → ClosedSubspaces B S hS X.1) (r : ℕ) :
    fittingRankStratum B S hS X Z (r + 1) =
      (Z r).1 ⊓ openComplement B S hS (Z (r + 1)).1 := by
  rw [fittingRankStratum, closedChainPred_succ]

/-- **Each stratum `X_r = Z_{r-1} \ Z_r` of a chain of closed subspaces of an algebraic space is
a locally closed subspace.** -/
theorem isLocallyClosedSubspace_fittingRankStratum (Z : ℕ → ClosedSubspaces B S hS X.1)
    (r : ℕ) :
    IsLocallyClosedSubspace B S hS (fittingRankStratum B S hS X Z r) :=
  isLocallyClosedSubspace_inf_openComplement B S hS X _ _
    (isClosedSubspace_closedChainPred B S hS X Z r) (Z r).2

/-- A stratum of a decreasing chain of closed subspaces lies in every earlier member of the
chain. -/
theorem fittingRankStratum_le_of_lt (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : Antitone fun r ↦ (Z r).1) {r s : ℕ} (hrs : r < s) :
    fittingRankStratum B S hS X Z s ≤ (Z r).1 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  exact le_trans inf_le_left (hZ (Nat.lt_succ_iff.1 hrs))

/-- The meet of two distinct strata of a decreasing chain of closed subspaces has no points. -/
theorem range_pointsMap_ι_inf_fittingRankStratum_eq_empty
    (Z : ℕ → ClosedSubspaces B S hS X.1) (hZ : Antitone fun r ↦ (Z r).1) {r s : ℕ}
    (hrs : r < s) :
    Set.range (pointsMap B S hS
        (fittingRankStratum B S hS X Z r ⊓ fittingRankStratum B S hS X Z s).toFunctor
        (fittingRankStratum B S hS X Z r ⊓ fittingRankStratum B S hS X Z s).ι) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  have hout := range_pointsMap_ι_le B S hS
    (le_trans (inf_le_left (b := fittingRankStratum B S hS X Z s))
      (inf_le_right (a := closedChainPred B S hS X Z r))) hx
  have hin := range_pointsMap_ι_le B S hS
    (le_trans (inf_le_right (a := fittingRankStratum B S hS X Z r))
      (fittingRankStratum_le_of_lt B S hS X Z hZ hrs)) hx
  rw [range_pointsMap_ι_openComplement] at hout
  exact hout hin

/-- **Distinct strata of a decreasing chain of closed subspaces are disjoint**: their meet is the
empty algebraic subspace.

For `r < s` the stratum `X_s` lies in `Z_{s-1} ⊆ Z_r` while `X_r` lies in the open complement of
`Z_r`, so the meet has no points, and part (1) of Stacks 03BZ detects containment in an open
subspace on points. -/
theorem fittingRankStratum_inf_le_sheafify_bot (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : Antitone fun r ↦ (Z r).1) {r s : ℕ} (hrs : r ≠ s) :
    fittingRankStratum B S hS X Z r ⊓ fittingRankStratum B S hS X Z s ≤
      (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS) := by
  refine le_of_range_pointsMap_ι_subset B S hS (isOpenSubspace_sheafify_bot B S hS X.1 X.2) ?_
  rcases lt_or_gt_of_ne hrs with h | h
  · exact (range_pointsMap_ι_inf_fittingRankStratum_eq_empty B S hS X Z hZ h).trans_le
      (Set.empty_subset _)
  · rw [inf_comm]
    exact (range_pointsMap_ι_inf_fittingRankStratum_eq_empty B S hS X Z hZ h).trans_le
      (Set.empty_subset _)

/-- **Every point of the ambient space lies in exactly one stratum of a decreasing chain of
closed subspaces whose point sets have empty intersection.**

The index is characterised without reference to the convention `Z_{-1} = X`: the point lies in
`X_r = Z_{r-1} \ Z_r` exactly when it lies outside `Z_r` and inside every earlier member of the
chain, the latter being vacuous for `r = 0` and equivalent to membership in `Z_{r-1}` otherwise.
Existence is the least index at which the point leaves the chain, and uniqueness holds because
the chain decreases. -/
theorem existsUnique_stratum_index (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hempty : (⋂ r : ℕ, Set.range (pointsMap B S hS (Z r).1.toFunctor (Z r).1.ι)) = ∅)
    (x : points B S hS X.1) :
    ∃! r : ℕ, x ∉ Set.range (pointsMap B S hS (Z r).1.toFunctor (Z r).1.ι) ∧
      ∀ k < r, x ∈ Set.range (pointsMap B S hS (Z k).1.toFunctor (Z k).1.ι) := by
  classical
  have hex : ∃ r : ℕ, x ∉ Set.range (pointsMap B S hS (Z r).1.toFunctor (Z r).1.ι) := by
    by_contra h
    exact Set.eq_empty_iff_forall_notMem.1 hempty x
      (Set.mem_iInter.2 fun r ↦ not_not.1 fun hr ↦ h ⟨r, hr⟩)
  refine ⟨Nat.find hex, ⟨Nat.find_spec hex, fun k hk ↦ not_not.1 (Nat.find_min hex hk)⟩, ?_⟩
  rintro s ⟨hs, hs'⟩
  rcases lt_trichotomy s (Nat.find hex) with h | h | h
  · exact absurd (not_not.1 (Nat.find_min hex h)) hs
  · exact h
  · exact absurd (hs' _ h) (Nat.find_spec hex)

/-! ### The Fitting rank strata -/

/-- A chain of closed subspaces whose defining ideal sheaves are the Fitting ideals of a module
decreases, because the Fitting ideals increase. -/
theorem antitone_of_definingIdealSheaf_eq_fittingIdeal (G : Modules.{u, u} B S hS X.1 X.2)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) :
    Antitone fun r ↦ (Z r).1 := by
  intro r s hrs
  refine le_of_definingIdealSheaf_le B S hS X (Z s) (Z r) ?_
  rw [hZ r, hZ s]
  exact fittingIdeal_mono G hrs

/-- **Stacks 0CZA, the Fitting rank strata.**  Let `G` be an `𝒪_X`-module and let
`X ⊇ Z_0 ⊇ Z_1 ⊇ …` be closed subspaces of `X` whose defining ideal sheaves are the Fitting
ideals of `G`, as in Stacks 0CZ9.  Then the strata `X_r = Z_{r-1} \ Z_r`, with the convention
`Z_{-1} = X`, are locally closed subspaces of `X`, and distinct strata are disjoint. -/
@[stacks 0CZA "the strata X_r = Z_{r-1} \\ Z_r are disjoint locally closed subspaces"]
theorem isLocallyClosedSubspace_and_disjoint_fittingRankStratum
    (G : Modules.{u, u} B S hS X.1 X.2) (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) :
    (∀ r : ℕ, IsLocallyClosedSubspace B S hS (fittingRankStratum B S hS X Z r)) ∧
      ∀ r s : ℕ, r ≠ s →
        fittingRankStratum B S hS X Z r ⊓ fittingRankStratum B S hS X Z s ≤
          (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS) :=
  ⟨isLocallyClosedSubspace_fittingRankStratum B S hS X Z,
    fun _ _ h ↦ fittingRankStratum_inf_le_sheafify_bot B S hS X Z
      (antitone_of_definingIdealSheaf_eq_fittingIdeal B S hS X G Z hZ) h⟩

/-- **Stacks 0CZA, the Fitting rank strata cover `X`.**  Every point of `X` lies in exactly one
Fitting rank stratum `X_r = Z_{r-1} \ Z_r`: there is a unique `r` with the point outside `Z_r`
and inside every earlier member of the chain.

The input is clause (1) of Stacks 0CZ9,
`AlgebraicGeometry.Space.iInter_range_pointsMap_ι_fittingClosedSubspace_eq_empty`: the point
sets of the Fitting closed subspaces have empty intersection, so every point leaves the chain,
and it does so at a unique index because the chain decreases. -/
@[stacks 0CZA "every point of X lies in exactly one stratum X_r = Z_{r-1} \\ Z_r"]
theorem existsUnique_fittingRankStratum_index (G : Modules.{u, u} B S hS X.1 X.2)
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    (x : points B S hS X.1) :
    ∃! r : ℕ, x ∉ Set.range (pointsMap B S hS (Z r).1.toFunctor (Z r).1.ι) ∧
      ∀ k < r, x ∈ Set.range (pointsMap B S hS (Z k).1.toFunctor (Z k).1.ι) :=
  existsUnique_stratum_index B S hS X Z
    (iInter_range_pointsMap_ι_fittingClosedSubspace_eq_empty B S hS X G Z hZ hfin) x

/-! ### The disjoint union of the strata -/

/-- The rank-`r` stratum `X_r = Z_{r-1} \ Z_r`, as an algebraic space over `S`. -/
def fittingRankStratumSpace (Z : ℕ → ClosedSubspaces B S hS X.1) (r : ℕ) :
    AlgebraicSpaces B S hS :=
  ⟨(fittingRankStratum B S hS X Z r).toFunctor,
    (isLocallyClosedSubspace_fittingRankStratum B S hS X Z r).1⟩

/-- The inclusion of the rank-`r` stratum in the ambient algebraic space. -/
def fittingRankStratumHom (Z : ℕ → ClosedSubspaces B S hS X.1) (r : ℕ) :
    fittingRankStratumSpace B S hS X Z r ⟶ X :=
  ObjectProperty.homMk (fittingRankStratum B S hS X Z r).ι

/-- **The disjoint union `X' = ∐_{r ≥ 0} X_r`** of the strata of a chain of closed subspaces of
an algebraic space, formed as a coproduct in the category of algebraic spaces over `S`. -/
def fittingRankStratification (Z : ℕ → ClosedSubspaces B S hS X.1) : AlgebraicSpaces B S hS :=
  ∐ fun r : ℕ ↦ fittingRankStratumSpace B S hS X Z r

/-- The structural morphism of the disjoint union `X' = ∐_{r ≥ 0} X_r` to the ambient algebraic
space, assembled from the inclusions of the strata. -/
def fittingRankStratificationHom (Z : ℕ → ClosedSubspaces B S hS X.1) :
    fittingRankStratification B S hS X Z ⟶ X :=
  Sigma.desc fun r ↦ fittingRankStratumHom B S hS X Z r

/-- **Stacks 0CZA, the disjoint union of the Fitting rank strata.**  The disjoint union
`X' = ∐_{r ≥ 0} X_r` of the strata `X_r = Z_{r-1} \ Z_r` of a chain `X ⊇ Z_0 ⊇ Z_1 ⊇ …` of closed
subspaces of `X` is an algebraic space over `S`, and its structural morphism restricts on the
`r`-th summand to the inclusion of `X_r` in `X`. -/
@[stacks 0CZA "X' = ∐_{r ≥ 0} X_r is an algebraic space, with its morphism to X"]
theorem isAlgebraicSpace_fittingRankStratification (Z : ℕ → ClosedSubspaces B S hS X.1) :
    IsAlgebraicSpace B S hS (fittingRankStratification B S hS X Z).obj ∧
      ∀ r : ℕ, Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r ≫
          fittingRankStratificationHom B S hS X Z = fittingRankStratumHom B S hS X Z r :=
  ⟨(fittingRankStratification B S hS X Z).property,
    fun r ↦ Sigma.ι_comp_desc _ r⟩

end AlgebraicGeometry.Space

end
