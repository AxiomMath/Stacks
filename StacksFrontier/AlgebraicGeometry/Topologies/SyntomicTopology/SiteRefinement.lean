module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.Support.SyntomicSiteRepresentatives
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Stability
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.StandardRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.SyntomicTopology.Coverings
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver

/-!
# Refinement of syntomic coverings in a big syntomic site

An arbitrary syntomic covering of an object of a big syntomic site admits a
refinement by a covering belonging to the chosen site. A standard syntomic covering of such an
object is, more strongly, tautologically equivalent to a covering belonging to the site.

## Main results

* `AlgebraicGeometry.exists_siteCovering_refining`: a syntomic
  covering of a site object is refined by a covering in the site.
* `AlgebraicGeometry.BigSyntomicSite.exists_isCovering_tautologicallyEquivalent_standardCovering`:
  a standard syntomic covering of a site object is tautologically equivalent to a covering in
  the site.

## Implementation notes

The original syntomic covering may have sources outside the size-bounded
category. The refined family consists of objects of that category; after
applying the inclusion functor, its refinement of the original family is a
morphism of pre-zero-hypercovers over their common target.

The refinement is built by pulling the given family back along an affine open cover of the
target, replacing each pullback by a finite affine standard syntomic refinement, and then
representing the resulting family inside the site.

A standard syntomic covering needs no such replacement: its members are affine and standard
syntomic, hence of finite type over the target, so each of them is already small enough to
lie in the size-bounded category and the family transfers into the site directly.

## References

* [Stacks Project, Tag 03X2](https://stacks.math.columbia.edu/tag/03X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The cover underlying a syntomic affine cover is a syntomic covering. -/
public theorem Scheme.AffineCover.isSyntomicCovering {X : Scheme.{u}}
    (R : Scheme.AffineCover.{v} @Syntomic X) :
    IsSyntomicCovering R.cover.toPreZeroHypercover.X R.cover.toPreZeroHypercover.f := by
  refine ⟨R.map_prop, Set.eq_univ_of_forall fun x => ?_⟩
  obtain ⟨y, hy⟩ := R.covers x
  exact Set.mem_iUnion.mpr ⟨R.idx x, Set.mem_range.mpr ⟨y, hy⟩⟩

/-- An affine scheme with a syntomic morphism to a scheme below the cutoff of a big syntomic site
is isomorphic to an object of the site. -/
private theorem exists_iso_obj_of_syntomic_of_size_lt (B : BigSyntomicSite.{u})
    {X Y : Scheme.{u}} [IsAffine X] (f : X ⟶ Y) (hf : Syntomic f) (hY : Y.size < B.cutoff) :
    ∃ V : B.category, Nonempty (X ≅ B.inclusion.obj V) :=
  have := locallyOfFinitePresentation hf
  ⟨⟨X, (Scheme.size_le_of_locallyOfFiniteType f).trans_lt hY⟩, ⟨Iso.refl _⟩⟩

/-- Every syntomic covering of an object of a big syntomic site admits a
refinement by a covering in the site. -/
@[stacks 03X2 "site_refinement"]
public theorem exists_siteCovering_refining
    (B : BigSyntomicSite.{u}) (T : B.category)
    (E : PreZeroHypercover.{v} (B.inclusion.obj T))
    (hE : IsSyntomicCovering E.X E.f) :
    ∃ 𝒰 : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, 𝒰⟩ ∧
        Nonempty ((𝒰.map B.inclusion).Hom E) := by
  classical
  let S := B.inclusion.obj T
  let O : S.AffineOpenCover := S.affineOpenCover
  have hO : IsSyntomicCovering O.cover.toPreZeroHypercover.X O.cover.toPreZeroHypercover.f :=
    isSyntomicCovering_of_mem_zariskiPrecoverage O.cover.mem₀
  let P (i : O.cover.I₀) := E.pullback₂ (O.cover.f i)
  have hP (i : O.cover.I₀) : IsSyntomicCovering (P i).X (P i).f :=
    isSyntomicCovering_pullback E.X E.f (O.cover.f i) hE
  let (i : O.cover.I₀) : IsAffine (O.cover.X i) := Scheme.isAffine_affineOpenCover S O i
  choose R φ _ _ _ using fun i : O.cover.I₀ =>
    exists_finite_affine_standardSyntomic_refinement (P i) (hP i)
  let F : PreZeroHypercover.{u} S := {
    I₀ := Σ i : O.cover.I₀, (R i).cover.I₀
    X k := (R k.1).cover.X k.2
    f k := (R k.1).cover.f k.2 ≫ O.cover.f k.1
  }
  have hF : IsSyntomicCovering F.X F.f := by
    simpa [F, Scheme.AffineCover.cover] using
      IsSyntomicCovering.comp O.cover.toPreZeroHypercover.X O.cover.toPreZeroHypercover.f hO
        (fun i => (R i).cover.toPreZeroHypercover.X)
        (fun i => (R i).cover.toPreZeroHypercover.f) fun i => (R i).isSyntomicCovering
  have hrep : ∀ k, ∃ V : B.category, Nonempty (F.X k ≅ B.inclusion.obj V) := by
    rintro ⟨i, j⟩
    have : IsAffine ((R i).cover.X j) := by
      change IsAffine (Spec ((R i).X j))
      infer_instance
    exact exists_iso_obj_of_syntomic_of_size_lt B ((R i).cover.f j) ((R i).map_prop j)
      (Scheme.size_lt_of_isOpenImmersion (O.cover.f i) T.2)
  have hFE : F.Hom E := by
    refine ⟨fun k => (φ k.1).s₀ k.2,
      fun k => (φ k.1).h₀ k.2 ≫ pullback.fst (E.f ((φ k.1).s₀ k.2)) (O.cover.f k.1), ?_⟩
    rintro ⟨i, j⟩
    have hw : (φ i).h₀ j ≫ pullback.snd (E.f ((φ i).s₀ j)) (O.cover.f i) = (R i).cover.f j :=
      (φ i).w₀ j
    change ((φ i).h₀ j ≫ pullback.fst _ _) ≫ E.f ((φ i).s₀ j) = (R i).cover.f j ≫ O.cover.f i
    exact (Category.assoc _ _ _).trans <| (congrArg ((φ i).h₀ j ≫ ·) pullback.condition).trans <|
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ O.cover.f i) hw)
  obtain ⟨𝒰, hcover, htaut⟩ :=
    BigSyntomicSite.exists_isCovering_tautologicallyEquivalent_of_sources_iso B T F hF hrep
  obtain ⟨⟨hF𝒰⟩, ⟨h𝒰F⟩⟩ :=
    CategoryTheory.PreZeroHypercover.nonempty_hom_and_nonempty_hom_of_tautologicallyEquivalent
      F (𝒰.map B.inclusion) htaut
  exact ⟨𝒰, hcover, ⟨h𝒰F.comp hFE⟩⟩

/-- A standard syntomic covering of an object of a big syntomic site is tautologically
equivalent to a covering belonging to the site. -/
@[stacks 03X2 "part (2)"]
public theorem BigSyntomicSite.exists_isCovering_tautologicallyEquivalent_standardCovering
    (B : BigSyntomicSite.{u}) (T : B.category)
    (U : PreZeroHypercover.{v} (B.inclusion.obj T))
    (hU : IsStandardSyntomicCovering U.X U.f) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U (V.map B.inclusion) := by
  have hsyn : IsSyntomicCovering U.X U.f :=
    ⟨fun i => @syntomic_of_standardSyntomic _ _ (hU.affine_source i) hU.affine_target _
      (hU.standard_syntomic i), hU.jointly_surjective⟩
  refine B.exists_isCovering_tautologicallyEquivalent_of_sources_iso T U hsyn fun i => ?_
  have : IsAffine (U.X i) := hU.affine_source i
  exact exists_iso_obj_of_syntomic_of_size_lt B (U.f i) (hsyn.1 i) T.2

end AlgebraicGeometry
