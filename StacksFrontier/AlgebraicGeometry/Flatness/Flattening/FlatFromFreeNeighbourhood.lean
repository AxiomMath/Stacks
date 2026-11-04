module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibrePointFreeness
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericRankDecomposition
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteLocallyFreeOfRank

/-!
# Flatness over the base from freeness near a point

A quasi-coherent module which is free of finite rank on a neighbourhood of a point is flat over
the base there, as soon as the structure morphism is flat: the module is finite locally free on
that neighbourhood, a finite locally free module is flat over a flat base
(`AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree`), and flatness
over the base is a local condition on the source
(`AlgebraicGeometry.isFlatOverAt_restrict_iff`).

`AlgebraicGeometry.isFlatOverAt_of_freeAtPointOfRank` is the same statement for a *smooth*
morphism; smoothness is used there only to supply flatness, so this is the version with the
hypothesis actually needed, and it applies to a base change of a flat morphism — in particular to
the projection `X ×_S Bl_I(S) ⟶ Bl_I(S)` of [Stacks, Tag 0811], where `X ⟶ S` is flat by
hypothesis (1) of that tag but nothing is smooth.

## Main results

* `AlgebraicGeometry.isFlatOverAt_of_freeAtPointOfRank_of_flat`:
  `AlgebraicGeometry.FreeAtPointOfRank` gives flatness over the base at the point, for a flat
  structure morphism.
* `AlgebraicGeometry.isFlatOverAt_of_over_iso_free`: the same from a trivialisation
  `F.over W ≅ SheafOfModules.free (ULift (Fin r))` on an open `W` containing the point. This is
  the form in which the affine engine of [Stacks, Tag 0810] delivers its conclusion — freeness of
  rank `r` on a basic open of a chart — and the flatness clause of
  `AlgebraicGeometry.GenericFibreFlatteningBlowup` is this predicate at the points whose
  fibre-preimage lies in their closure.

## Implementation notes

The rank data produced by `AlgebraicGeometry.FreeAtPointOfRank` is
`Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank` of the *pullback* along the open
immersion, while the flatness input is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of the *restriction*; the two are matched
by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso`, the two classes having the
same single field.

## References

* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A module free of finite rank near a point of the source of a flat morphism is flat over the
base there.** This is `AlgebraicGeometry.isFlatOverAt_of_freeAtPointOfRank` with `Smooth`
weakened to `Flat`, which is all its proof uses. -/
public theorem isFlatOverAt_of_freeAtPointOfRank_of_flat {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (F : X.Modules) [F.IsQuasicoherent] (x : X) (r : ℕ) (hfree : FreeAtPointOfRank F x r) :
    IsFlatOverAt f.toLRSHom.toShHom F x := by
  obtain ⟨U, hxU, hRank⟩ := hfree
  have h1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.restrict U.ι) r :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm
      { exists_isFiniteLocallyFreeOfRankData := hRank.exists_isFiniteLocallyFreeOfRankData }
  have h2 : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (F.restrict U.ι) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (F.restrict U.ι) r
  have hfo := VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree (U.ι ≫ f)
    (F.restrict U.ι)
  simpa using (isFlatOverAt_restrict_iff U.ι f F ⟨x, hxU⟩).mp (hfo ⟨x, hxU⟩)

/-- **A trivialisation on an open neighbourhood gives flatness over the base at every point of
it.** For `f` flat and `F` quasi-coherent, an isomorphism of `F.over W` with a finite free module
makes `F` flat over the base at each point of `W`.

This is the shape in which the affine engine of [Stacks, Tag 0810] delivers its conclusion, and
the shape the flatness clause of `AlgebraicGeometry.GenericFibreFlatteningBlowup` asks for. -/
public theorem isFlatOverAt_of_over_iso_free {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (F : X.Modules) [F.IsQuasicoherent] {x : X} {W : X.Opens} (hx : x ∈ W) (r : ℕ)
    (e : F.over W ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) :
    IsFlatOverAt f.toLRSHom.toShHom F x :=
  isFlatOverAt_of_freeAtPointOfRank_of_flat f F x r
    (freeAtPointOfRank_of_over_iso_free F hx r e)

end AlgebraicGeometry

end
