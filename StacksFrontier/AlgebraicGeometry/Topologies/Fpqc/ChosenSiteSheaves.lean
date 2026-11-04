module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcSmallEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Restricting an fpqc sheaf to a chosen site

Two general facts used to restrict an fpqc sheaf on the schemes over `S` to a chosen site of
`S`: a criterion for a covering family of the site to lie in the precoverage comapped from the
fpqc topology, and a creation-of-pullbacks criterion for the site's canonical functor to the
schemes over `S`.

## Main results

* `Stacks.Sites.mem_comap_over_fpqcTopology`: a covering family whose image in all schemes is an
  fpqc covering family lies in the precoverage comapped from the fpqc topology on the schemes
  over `S`.
* `Stacks.Sites.createsLimitsOfShape_of_overForget`: a fully faithful functor into the schemes
  over `S` whose composite with the slice projection preserves pairwise pullbacks creates
  them.

## Implementation notes

The restriction statements themselves — for the chosen big and small Zariski sites and the
chosen big, big affine and small affine etale sites — are
`AlgebraicGeometry.isSheaf_bigZariski_of_isSheaf_fpqc` and its siblings in
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison`, with the two affine Zariski cases
in `StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.AffineZariskiSheaves`. Each is one
application of `Stacks.Sites.isSheaf_toGrothendieck_of_precoverage_le` whose covering
hypothesis is supplied by `Stacks.Sites.mem_comap_over_fpqcTopology` from the site's own
covering predicate, which projects to a Zariski or etale covering of schemes.

The pullback-creation instance for the canonical functor to the schemes over `S` cannot be
synthesized at the spelling in which those statements are written, because
`CategoryTheory.Over.post` carries its base object implicitly, so the preservation fact for the
composite with the slice projection is passed to
`Stacks.Sites.createsLimitsOfShape_of_overForget` positionally as
`inferInstanceAs (PreservesLimitsOfShape WalkingCospan (… .toScheme B S hS))`.

## References

* [Stacks Project, Tag 03O4](https://stacks.math.columbia.edu/tag/03O4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.Sites

/-- A pre-zero-hypercover `E` of `X` whose image under `F ⋙ Over.forget S` is an fpqc covering
family lies in the precoverage on `C` comapped along `F` from the fpqc topology on the schemes
over `S`. -/
public theorem mem_comap_over_fpqcTopology {C : Type*} [Category C] {S : Scheme.{u}}
    (F : C ⥤ Over S) {X : C} (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (F ⋙ Over.forget S)).presieve₀ ∈
      Scheme.fpqcPrecoverage ((F ⋙ Over.forget S).obj X)) :
    E.presieve₀ ∈ (Scheme.fpqcTopology.{u}.over S).toPrecoverage.comap F X := by
  have key : Sieve.overEquiv (F.obj X)
      ((Sieve.generate E.presieve₀).functorPushforward F) =
      (Sieve.generate E.presieve₀).functorPushforward (F ⋙ Over.forget S) :=
    (Sieve.functorPushforward_comp F (Over.forget S) _).symm
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
    Sieve.generate_map_eq_functorPushforward, GrothendieckTopology.mem_over_iff, key,
    ← Sieve.generate_map_eq_functorPushforward]
  refine Precoverage.generate_mem_toGrothendieck ?_
  simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map, Presieve.map_ofArrows] using hE

/-- A fully faithful functor `F : C ⥤ Over S` out of a category with pullbacks creates pullbacks
as soon as its composite with `Over.forget S` preserves them. -/
@[instance_reducible]
public noncomputable def createsLimitsOfShape_of_overForget {C : Type*} [Category C]
    {S : Scheme.{u}} (F : C ⥤ Over S) [F.Full] [F.Faithful] [HasPullbacks C]
    (h : PreservesLimitsOfShape WalkingCospan (F ⋙ Over.forget S)) :
    CreatesLimitsOfShape WalkingCospan F :=
  have := h
  have : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)
  ⟨fun {_} => createsLimitOfFullyFaithfulOfPreserves⟩

end Stacks.Sites

end
