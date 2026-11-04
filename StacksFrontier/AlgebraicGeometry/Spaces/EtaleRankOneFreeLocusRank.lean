module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ChartCoversTop
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# From the rank-one étale free locus to the rank clause of Stacks 0409

Let `Z` be an algebraic space over a scheme `S` of a big fppf site and let `F` be an
`𝒪_Z`-module.  If every point of `|Z|` has an étale neighbourhood on which `F` becomes
isomorphic to the structure sheaf — that is, if the rank-one étale free locus
`AlgebraicGeometry.Space.etaleRankOneFreeLocus` is all of `|Z|` — then `F` is finite locally
free of rank one on the small étale site of `Z`, in the sense of the rank clause of Stacks 0409.

This is the **local-to-global refinement**: the locus gives a trivialization through every
*point*, while the rank clause asks for a trivializing covering family of every *object* of the
site.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus`:
  the refinement.

## Implementation notes

The two steps are already in the development, and the proof is their composition.

The étale neighbourhoods chosen at the points of `|Z|` form an étale covering of `Z`
(`AlgebraicGeometry.Space.IsEtaleCovering`: they are étale, their sources are algebraic spaces
and their images cover `|Z|` by construction), so the charts of their members cover the final
object of the small étale site of `Z` —
`AlgebraicGeometry.Space.coversTop_of_isEtaleCovering`, the slice form of Stacks 04M0 applied to
a refinement.  That turns the pointwise datum into a covering family of the final object, which
is what `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover` — the rank
clause being local on a covering family, Stacks 03DN for Stacks 0409 — consumes.

On a member of that family the condition is read back on the neighbourhood by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_over_etaleModulePullback_iff`, the slice
comparison of Stacks 04M0 along an étale morphism, which is an *equivalence* of slices and
therefore transports the rank in both directions; the direction used here is the one that
descends it from the neighbourhood to `Z`.  There the module is the étale restriction of `F`,
isomorphic to the chosen trivialization through
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback` (Equation 03LW), and the
structure sheaf has rank one by
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_unit`.

The index of the covering family is `Σ x : |Z|, (étale charts of the neighbourhood at x)`, which
sits in `Type (u + 1)`; the small étale ringed site is `RingedSite.{u + 1, u, u}`, so this is
exactly the universe `max (u + 1) u` that the locality statement asks for and no lifting is
needed.

No Stacks attribute is carried.  The statement is neither Stacks 0409 nor Stacks 03DN — it is
the comparison of the locus of Stacks 0CZT at rank one with the rank clause, which no tag
states on its own.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The rank-one étale free locus being everything makes the module finite locally free of
rank one.**  If every point of `|Z|` admits an étale neighbourhood along which the inverse image
of `F` is isomorphic to the structure sheaf, then `F` has rank one on the small étale site of
`Z` in the sense of the rank clause of Stacks 0409.

This is the local-to-global step: the chosen neighbourhoods form an étale covering of `Z`, so
their charts cover the final object of the small étale site
(`AlgebraicGeometry.Space.coversTop_of_isEtaleCovering`), and the rank clause is local on such a
family (`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover`).  On each
member the rank is read back on the neighbourhood by the slice comparison of Stacks 04M0 along
an étale morphism. -/
theorem isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus
    {Z : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS Z.1 Z.2)
    (h : ∀ x : points B S hS Z.1, x ∈ etaleRankOneFreeLocus B S hS F) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2) F 1 := by
  classical
  choose V a hae hrange he using h
  have hcov : IsEtaleCovering B S hS (fun x => (V x).1) (fun x => (a x).hom) :=
    { target_isAlgebraicSpace := Z.2
      source_isAlgebraicSpace := fun x => (V x).2
      etale := hae
      jointly_surjective :=
        Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hrange x⟩ }
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover
    (smallEtaleRingedSite B S hS Z.1 Z.2) F 1).2
    ⟨_, memberChart B S hS V a hcov.etale, coversTop_of_isEtaleCovering B S hS V a hcov, ?_⟩
  rintro ⟨x, W⟩
  refine (isFiniteLocallyFreeOfRank_over_etaleModulePullback_iff B S hS (a x) (hae x) F W 1).1 ?_
  refine RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
    ((SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (V x).1 (V x).2).O) W).mapIso
      (((modulePullbackIsoEtaleModulePullback B S hS (a x) (hae x)).app F).symm ≪≫
        (he x).some)).symm ?_
  exact RingedSite.IsFiniteLocallyFreeOfRank.over
    (smallEtaleRingedSite B S hS (V x).1 (V x).2) _
    (RingedSite.isFiniteLocallyFreeOfRank_unit (smallEtaleRingedSite B S hS (V x).1 (V x).2)) W

end AlgebraicGeometry.Space

end
