module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperClosedSubspaceStage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedIdealSheafOfClosedSet
public import StacksFrontier.AlgebraicGeometry.Spaces.RetrocompactOpenComplement

/-!
# A closed subset proper over the base lies in a finitely presented closed subspace

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over a scheme `S`,
with `X` quasi-compact and quasi-separated and `Y` quasi-compact, and let `Z ⊆ |X|` be a closed
subset proper over `Y`. Then `Z` is contained in the point set `T` of a closed subspace
`W ⊆ X` of finite presentation which is proper over `Y`. The set `T` is closed and proper over
`Y`, and the inclusion of its open complement is quasi-compact.

This is the reduction step that generalizes the derived Grothendieck existence theorem from
complexes supported on a closed subset with quasi-compact complement to complexes with proper
support.

## Main results

* `AlgebraicGeometry.Space.exists_closedSubspace_isFinitePresentation_of_isProperOver`: the
  closed subspace `W` and the properties of its point set `T`.
* `AlgebraicGeometry.Space.isProperOver_range_pointsMap_ι`: the point set of a closed subspace
  proper over `Y` is proper over `Y`.
* `AlgebraicGeometry.Space.isQuasiCompact_ι_openSubspacesOrderIso_symm_compl`: the open
  complement of the point set of a finitely presented closed subspace has quasi-compact
  inclusion, in the form of `AlgebraicGeometry.Space.ApproximationByPerfectComplexes`.

## Implementation notes

The reduced closed subspace `C` on `Z` is proper over `Y` by definition of `IsProperOver`.
Stacks 0A0U writes `C` as the limit of a directed antitone family of closed subspaces `Z_i ⊇ C`
of finite presentation, and the claim in the proof of Stacks 0A0W makes some `Z_i` proper
over `Y`; that `Z_i` is `W`. The reduced closed subspace on the point set of `W` is contained in
`W` by Stacks 03JJ, so it is proper over `Y` as well.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
-/

@[expose] public section

open CategoryTheory

universe u

attribute [local instance] AlgebraicGeometry.Space.pointTopology

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The point set of a closed subspace proper over the base is proper over the base.** The
reduced closed subspace on the point set of `W` is contained in `W` by Stacks 03JJ, and the
inclusion of one closed subspace in another is a closed immersion, hence proper. -/
theorem isProperOver_range_pointsMap_ι {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (W : ClosedSubspaces B S hS X)
    (hW : IsProper B S hS (W.1.ι ≫ f)) :
    IsProperOver B S hS hX hY f hf (Set.range (pointsMap B S hS W.1.toFunctor W.1.ι))
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS hX W.1.ι W.2.2) := by
  have hle := reducedClosedSubspace_le_of_isClosedSubspace B S hS hX W.1 W.2
  have hred := isAlgebraicSpace_reducedClosedSubspace B S hS X hX _
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS hX W.1.ι W.2.2)
  have hgp := isProper_of_isClosedImmersion B S hS hred W.2.1 (Subfunctor.homOfLe hle)
    (isClosedImmersion_homOfLe' B S hS (isClosedImmersion_ι_reducedClosedSubspace B S hS hX _
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS hX W.1.ι W.2.2)) hle)
  have hcomp := isProper_comp' B S hS (Subfunctor.homOfLe hle) (W.1.ι ≫ f) W.2.1 hY hgp hW
  change IsProper B S hS _
  simpa only [← Category.assoc, Subfunctor.homOfLe_ι] using hcomp

/-- **The complement of the point set of a finitely presented closed subspace has
quasi-compact inclusion.** The open subspace with point set the complement of the point set
of `W` is the open complement of `W`, whose inclusion is quasi-compact because `W` is of finite
presentation. -/
theorem isQuasiCompact_ι_openSubspacesOrderIso_symm_compl {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (W : ClosedSubspaces B S hS X)
    (hW : IsFinitePresentation B S hS W.1.ι) :
    IsQuasiCompact B S hS ((openSubspacesOrderIso B S hS X hX).symm
      ⟨(Set.range (pointsMap B S hS W.1.toFunctor W.1.ι))ᶜ,
        (isClosed_range_pointsMap_of_isClosedImmersion B S hS hX W.1.ι
          W.2.2).isOpen_compl⟩).1.ι := by
  have hO := isOpenSubspace_openComplement B S hS hX W.1 W.2
  have he : (openSubspacesOrderIso B S hS X hX).symm
      ⟨(Set.range (pointsMap B S hS W.1.toFunctor W.1.ι))ᶜ,
        (isClosed_range_pointsMap_of_isClosedImmersion B S hS hX W.1.ι
          W.2.2).isOpen_compl⟩ = ⟨openComplement B S hS W.1, hO⟩ := by
    rw [OrderIso.symm_apply_eq]
    exact TopologicalSpace.Opens.ext (range_pointsMap_ι_openComplement B S hS W.1).symm
  rw [he]
  exact isQuasiCompact_ι_openComplement_of_isFinitePresentation B S hS hX W.1 W.2 hW

/-- **A closed subset proper over the base lies in a finitely presented closed subspace proper
over the base.** Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over
`S`, with `X` quasi-compact and quasi-separated and `Y` quasi-compact, and let `Z ⊆ |X|` be
closed and proper over `Y`. Then there is a closed subspace `W ⊆ X` of finite presentation with
`W ⟶ Y` proper whose point set `T` contains `Z`; `T` is closed and proper over `Y`, and the
inclusion of the open complement of `T` is quasi-compact.

The reduced closed subspace on `Z` is the limit of a directed antitone family of finitely
presented closed subspaces of `X` (Stacks 0A0U), and one of them is proper over `Y` by the
claim in the proof of Stacks 0A0W. -/
theorem exists_closedSubspace_isFinitePresentation_of_isProperOver
    (hZ : B.Contains (⊤_ Scheme.{u})) (X Y : AlgebraicSpaces B S hS) (f : X.1 ⟶ Y.1)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (Z : Set (points B S hS X.1)) (hZc : IsClosed Z)
    (hZp : IsProperOver B S hS X.2 Y.2 f hft.1 Z hZc) :
    ∃ W : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS W.1.ι ∧
      IsProper B S hS (W.1.ι ≫ f) ∧
      ∃ hT : IsClosed (Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)),
        Z ⊆ Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) ∧
        IsProperOver B S hS X.2 Y.2 f hft.1 _ hT ∧
        IsQuasiCompact B S hS ((openSubspacesOrderIso B S hS X.1 X.2).symm
          ⟨(Set.range (pointsMap B S hS W.1.toFunctor W.1.ι))ᶜ, hT.isOpen_compl⟩).1.ι := by
  let C := reducedClosedSubspaces B S hS X Z hZc
  obtain ⟨A⟩ := hasClosedSubspaceApproximation_of_isQuasiCompactSpace B S hS hZ X hXqc hXqs C
  let := A.indexPreorder
  have := A.indexDirected
  have : Nonempty A.index := ⟨A.point⟩
  have hge : (⨅ i, (A.stage i).1) ≤ C.1 :=
    iInf_le_of_isLimit_closedSubspaceCone B S hS _ A.stage_antitone C.1 A.le_stage A.isLimit
  obtain ⟨i₀, hi₀⟩ := exists_forall_ge_isProper_closedSubspace_comp B S hS Y.2 hYqc X.2 f hsep
    hft A.stage A.stage_antitone C A.le_stage hge hZp
  set W := A.stage i₀
  have hWp : IsProper B S hS (W.1.ι ≫ f) := hi₀ i₀ le_rfl
  have hZT : Z ⊆ Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) := by
    have h := range_pointsMap_ι_le B S hS (A.le_stage i₀)
    rwa [show C.1 = reducedClosedSubspace B S hS X.1 X.2 Z hZc from rfl,
      range_pointsMap_ι_reducedClosedSubspace] at h
  exact ⟨W, A.stage_isFinitePresentation i₀, hWp,
    isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 W.1.ι W.2.2, hZT,
    isProperOver_range_pointsMap_ι B S hS X.2 Y.2 f hft.1 W hWp,
    isQuasiCompact_ι_openSubspacesOrderIso_symm_compl B S hS X.2 W
      (A.stage_isFinitePresentation i₀)⟩

end AlgebraicGeometry.Space

end
