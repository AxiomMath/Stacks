module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# Étale restriction of modules preserves the rank and the structure sheaf

For an étale morphism `f : X ⟶ Y` of algebraic spaces, restriction of `𝒪_Y`-modules along `f`
(`AlgebraicGeometry.Space.etaleModulePullback`) carries a module which is finite locally free of
rank `r` (Stacks 0409) to one of rank `r`, and carries the structure sheaf `𝒪_Y` to `𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_etaleModulePullback`: rank `r` is inherited
  by étale restriction.
* `AlgebraicGeometry.Space.etaleModulePullbackStructureSheafModuleIso`: the étale restriction of
  `𝒪_Y` is `𝒪_X`.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Rank `r` is inherited by étale restriction.** It is tested on the family of all objects of
the small étale site of the source, and over each of them étale restriction is the reindexing of
the restriction of the module to the corresponding chart of the target. -/
theorem isFiniteLocallyFreeOfRank_etaleModulePullback (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) {r : ℕ}
    (hM : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) M r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      ((etaleModulePullback B S hS f hf).obj M) r :=
  (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover _ _ r).2
    ⟨ULift.{u + 1} (smallEtaleRingedSite B S hS X.1 X.2).C, fun i => i.down,
      Stacks.SheafOfModules.coversTop_ulift_self (smallEtaleRingedSite B S hS X.1 X.2).J,
      fun i => (isFiniteLocallyFreeOfRank_over_etaleModulePullback_iff B S hS f hf M i.down r).2
        (RingedSite.IsFiniteLocallyFreeOfRank.over _ _ hM _)⟩

/-- The étale restriction of the structure sheaf `𝒪_Y` along an étale `f : X ⟶ Y` is the
structure sheaf `𝒪_X`: postcomposition with `f` leaves the scheme of a chart, hence its ring of
regular functions, unchanged. -/
noncomputable def etaleModulePullbackStructureSheafModuleIso (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    (etaleModulePullback B S hS f hf).obj (structureSheafModule B S hS Y) ≅
      structureSheafModule B S hS X :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (@PresheafOfModules.pushforwardUnitIso _ _ _ _ _ _ _ _ (inferInstanceAs (IsIso (𝟙 _))))

end AlgebraicGeometry.Space
