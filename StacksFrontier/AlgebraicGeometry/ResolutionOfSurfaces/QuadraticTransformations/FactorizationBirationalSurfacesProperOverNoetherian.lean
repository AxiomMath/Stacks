module

public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupFactorizationStep

/-!
# Factorization of an `S`-birational pair of regular surfaces proper over a Noetherian base

[Stacks, Tag 0C5S](https://stacks.math.columbia.edu/tag/0C5S) asks of its two schemes `X` and `Y`
only that they be integral, regular of dimension two and proper over a Noetherian scheme `S`. The
library's `Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface` bundles a fourth condition, that
the scheme itself be Noetherian, and the form of the tag already in this namespace,
`birationalOver_iff_exists_factorsAsPointBlowups_of_isIntegralRegularSurface`,
assumes that bundled predicate of both schemes.

The fourth condition is not an extra assumption. Properness contains
`AlgebraicGeometry.LocallyOfFiniteType`, which carries local Noetherianness down from the base,
and it contains `AlgebraicGeometry.QuasiCompact`, which carries compactness down from it;
together these are the two halves of `AlgebraicGeometry.IsNoetherian`, so a scheme proper over a
Noetherian scheme is Noetherian — `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`, which
is Tag 01T6 for a Noetherian target. The statement below therefore takes the tag's three
conditions on `X` and on `Y` one by one and builds the bundled predicate from them.

## Main results

* `Stacks.ResolutionOfSurfaces.birationalOver_iff_exists_factorsAsPointBlowups_of_isRegular`:
  for `X` and `Y` integral, regular of dimension two and proper over a Noetherian scheme `S`, the
  pair is `S`-birational if and only if there is a scheme `Z` with `S`-morphisms `Z ⟶ X` and
  `Z ⟶ Y`, each a finite sequence of blowups at closed points — the diagram
  `X = X₀ ← … ← Xₙ = Y_m → … → Y₀ = Y` of the source.

## References

* [Stacks Project, Tag 0C5S](https://stacks.math.columbia.edu/tag/0C5S)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- Let `S` be a Noetherian scheme and let `X` and `Y` be proper integral schemes over `S` which
are regular of dimension two. Then `X` and `Y` are `S`-birational if and only if there is a scheme
`Z` with `S`-morphisms `f : Z ⟶ X` and `g : Z ⟶ Y`, each a finite sequence of blowups at closed
points.

Of `X` and `Y` only the tag's own conditions are assumed: integral, regular, of dimension two,
and proper over the Noetherian base. Their Noetherianness, which
`Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface` demands in addition, is derived from
properness over `S`. -/
@[stacks 0C5S "the tag's hypothesis list, with the surface predicate derived rather than assumed:
  `S` is Noetherian and `X` and `Y` are proper over `S`, integral, regular and of dimension two.
  The bundled `Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface` of the other registration
  asks of the two schemes that they be Noetherian as well; here that is obtained from properness
  over `S` by Tag 01T6"]
public theorem birationalOver_iff_exists_factorsAsPointBlowups_of_isRegular
    {S X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [X.Over S] [Y.Over S]
    [IsProper (X ↘ S)] [IsProper (Y ↘ S)]
    (hXintegral : AlgebraicGeometry.IsIntegral X) (hXregular : AlgebraicGeometry.IsRegular X)
    (hXdim : topologicalKrullDim X = 2) (hYintegral : AlgebraicGeometry.IsIntegral Y)
    (hYregular : AlgebraicGeometry.IsRegular Y) (hYdim : topologicalKrullDim Y = 2) :
    Scheme.BirationalOver (X ↘ S) (Y ↘ S) ↔
      ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
        f ≫ (X ↘ S) = g ≫ (Y ↘ S) ∧
          FactorsAsPointBlowups X Set.univ Z f ∧ FactorsAsPointBlowups Y Set.univ Z g :=
  birationalOver_iff_exists_factorsAsPointBlowups_of_isIntegralRegularSurface
    ⟨hXintegral, isNoetherian_of_locallyOfFiniteType (X ↘ S), hXregular, hXdim⟩
    ⟨hYintegral, isNoetherian_of_locallyOfFiniteType (Y ↘ S), hYregular, hYdim⟩

end Stacks.ResolutionOfSurfaces

end
