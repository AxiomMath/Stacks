module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint

/-!
# The skyscraper sheaf at a geometric point of the small étale site

Let `B` be a big étale site containing a scheme `S` and let `s̄` be a geometric point of `S`. The
skyscraper sheaf `s̄_* M` at `s̄` with value `M` has as sections over an étale `U → S` the
`M`-valued families indexed by the lifts of `s̄` to `U`, and `M ↦ s̄_* M` is right adjoint to the
stalk functor at `s̄`.

## Main definitions

* `AlgebraicGeometry.etaleSkyscraperFunctor` — the skyscraper functor `M ↦ s̄_* M` at a
  geometric point.
* `AlgebraicGeometry.etaleSkyscraper` — the skyscraper sheaf `s̄_* M` itself.

## Main results

* `AlgebraicGeometry.etaleSkyscraper_obj` — the sections of `s̄_* M` over an object of the small
  étale site are the `M`-valued families on the lifts of `s̄` to it.
* `AlgebraicGeometry.etaleStalkSkyscraperAdjunction` — the stalk at `s̄` is left adjoint to the
  skyscraper at `s̄`.

## Implementation notes

A geometric point is a point of the small étale site by
`AlgebraicGeometry.geometricPointSitePoint`, whose fibre functor is the functor of lifts and
whose fibre on sheaves is the stalk; this file is the wrapper of Mathlib's
`CategoryTheory.GrothendieckTopology.Point.skyscraperSheafFunctor` and
`CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction` at that point, so that
the étale development can speak of skyscrapers without unfolding the point.

## References

* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (A : Type v) [Category.{w} A] [HasProducts.{u} A]

/-- The skyscraper sheaf functor at a geometric point `s̄` of `S`: the object `M` goes to the
sheaf on the small étale site of `S` whose sections over `U` are the `M`-valued families indexed
by the lifts of `s̄` to `U`. -/
public def etaleSkyscraperFunctor : A ⥤ Sheaf (SmallEtale.topology B S hS) A :=
  (geometricPointSitePoint B S hS s).skyscraperSheafFunctor

/-- The skyscraper sheaf `s̄_* M` at a geometric point `s̄` of `S` with value `M`. -/
public abbrev etaleSkyscraper (M : A) : Sheaf (SmallEtale.topology B S hS) A :=
  (etaleSkyscraperFunctor B S hS s A).obj M

/-- The sections of the skyscraper sheaf `s̄_* M` over an object `U` of the small étale site of
`S` are the `M`-valued families indexed by the lifts of `s̄` to `U`. -/
public theorem etaleSkyscraper_obj (M : A) (U : (SmallEtale B S hS)ᵒᵖ) :
    (etaleSkyscraper B S hS s A M).obj.obj U =
      ∏ᶜ fun _ : (geometricPointFiber B S hS s).obj U.unop => M :=
  rfl

/-- **Stacks 04FM.** The stalk functor at a geometric point `s̄` of `S` is left adjoint to the
skyscraper functor at `s̄`: a map `F_s̄ ⟶ M` is the same as a map `F ⟶ s̄_* M`. -/
@[stacks 04FM "the stalk at a geometric point is left adjoint to the skyscraper there"]
public def etaleStalkSkyscraperAdjunction [HasColimitsOfSize.{u, u} A] :
    (geometricPointSitePoint B S hS s).sheafFiber (A := A) ⊣
      etaleSkyscraperFunctor B S hS s A :=
  (geometricPointSitePoint B S hS s).skyscraperSheafAdjunction

end AlgebraicGeometry

end
